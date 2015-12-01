package tool;

import ast.*;
import ast.visitor.impl.*;
import tool.strategy.*;

import java.util.*;

import java.util.concurrent.*;

public class ExecutionPlan {

    private DebugUtil debugUtil;
    private final Program program;
    private final String testPath;
    private final int TIMEOUT = 155;

    public ExecutionPlan(Program program, DebugUtil debugUtil, String testPath) {
        this.program = program;
        this.debugUtil = debugUtil;
        this.testPath = testPath;
    }

    private void decide(SMTReturnCode returnCode) {
        switch (returnCode) {
            case UNKNOWN:
                System.out.println("UNKNOWN");
                System.exit(1);
                break ;
            case INCORRECT:
                System.out.println("INCORRECT");
                System.exit(0);
                break ;
            case CORRECT:
                System.out.println("CORRECT");
                System.exit(0);
                break ;
        }
    }

    private Program cloneProgram() {
        return cloneProgram(new HashMap<>());
    }

    private Program cloneProgram(Map<Node, Node> pred) {
        return (Program) new DefaultVisitor(pred).visit(program);
    }

    private SMTReturnCode getReturnCode(Future<SMTReturnCode> future) {
        SMTReturnCode retCode;
        try {
            retCode = future.get(1, TimeUnit.SECONDS);
        } catch (Exception exception) {
            retCode = SMTReturnCode.UNKNOWN;
        }
        return retCode;
    }

    public void verifyProgram() {
        ExecutorService executor = Executors.newFixedThreadPool(3);
        CompletionService<SMTReturnCode> completionService = new ExecutorCompletionService<>(executor);

        Future<SMTReturnCode> houdiniLoopSumarrisation =
                completionService.submit(new HoudiniWithLoopSummary(cloneProgram(), debugUtil, testPath));
        Future<SMTReturnCode> houdiniLoopBMC =
                completionService.submit(new HoudiniWithBMC(cloneProgram(), debugUtil));
        Future<SMTReturnCode> houdiniInvariantsInference =
                completionService.submit(new HoudiniWithInvariantInference(cloneProgram(), debugUtil, testPath));

        Map<Future<SMTReturnCode>, Set<SMTReturnCode>> trustedReturns = new HashMap<Future<SMTReturnCode>, Set<SMTReturnCode>>() {{
            Set<SMTReturnCode> houdiniLoopSummaryValues = new HashSet<>(
                    Arrays.asList(SMTReturnCode.CORRECT, SMTReturnCode.INCORRECT));
            put(houdiniLoopSumarrisation, houdiniLoopSummaryValues);

            Set<SMTReturnCode> houdiniBMCValues = new HashSet<>(Arrays.asList(SMTReturnCode.CORRECT, SMTReturnCode.INCORRECT));
            put(houdiniLoopBMC, houdiniBMCValues);

            Set<SMTReturnCode> houdiniInvariantInferenceValues = new HashSet<>(
                    Arrays.asList(SMTReturnCode.CORRECT, SMTReturnCode.INCORRECT));
            put(houdiniInvariantsInference, houdiniInvariantInferenceValues);
        }};

        try {
            long startTime = System.currentTimeMillis();
            long endTime = startTime + TIMEOUT * 1000;
            for (int strategies = 0; strategies < trustedReturns.size(); strategies++) {
                long timeout = endTime - System.currentTimeMillis();
                timeout = timeout > 0 ? timeout : 0;
                Future<SMTReturnCode> oneResult = completionService.poll(timeout, TimeUnit.MILLISECONDS);
                SMTReturnCode maybeRetCode = getReturnCode(oneResult);
                if (oneResult != null) {
                    if (trustedReturns.get(oneResult).contains(maybeRetCode)) {
                        decide(maybeRetCode);
                    }
                } else {
                    for (Future<SMTReturnCode> future: trustedReturns.keySet()) {
                        future.cancel(true);
                    }
                    decide(SMTReturnCode.UNKNOWN);
                }
            }
            decide(SMTReturnCode.UNKNOWN);
        } catch (InterruptedException e) {
            decide(SMTReturnCode.UNKNOWN);
            Thread.currentThread().interrupt();
        }
    }
}
