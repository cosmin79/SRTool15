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
    private final int TIMEOUT = 160;

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

    private boolean containsCandidatePrePost(Program program) {
        for (ProcedureDecl procedureDecl: program.getProcedureDecls()) {
            for (PrePostCondition prePostCondition: procedureDecl.getPrePostConditions()) {
                if (prePostCondition instanceof CandidatePrecondition || prePostCondition instanceof CandidatePostcondition) {
                    return true;
                }
            }
        }

        return false;
    }

    public void verifyProgram() {
        ExecutorService executor = Executors.newFixedThreadPool(2);
        CompletionService<SMTReturnCode> completionService = new ExecutorCompletionService<>(executor);

        Future<SMTReturnCode> houdini =
                completionService.submit(new HoudiniWithLoopSummary(cloneProgram(), debugUtil));
        Future<SMTReturnCode> soundBMC =
                completionService.submit(new HoudiniWithBMC(cloneProgram(), debugUtil));

        Map<Future<SMTReturnCode>, Set<SMTReturnCode>> trustedReturns = new HashMap<Future<SMTReturnCode>, Set<SMTReturnCode>>() {{
            Set<SMTReturnCode> houdiniValues = new HashSet<>(Arrays.asList(SMTReturnCode.CORRECT));
            if (program.getLoops().isEmpty()) {
                houdiniValues.add(SMTReturnCode.INCORRECT);
            }
            put(houdini, houdiniValues);

            Set<SMTReturnCode> soundBMCValues = new HashSet<>(Arrays.asList(SMTReturnCode.CORRECT));
            if (!containsCandidatePrePost(program)) {
                soundBMCValues.add(SMTReturnCode.INCORRECT);
            }
            put(soundBMC, soundBMCValues);
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
