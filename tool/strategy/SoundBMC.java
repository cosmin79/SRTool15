package tool.strategy;

import ast.*;
import ast.visitor.impl.*;
import tool.*;

import java.util.*;
import java.util.concurrent.Callable;

class TransformationResult {

    private Program program;

    private boolean success;

    public TransformationResult(Program program, boolean success) {
        this.program = program;
        this.success = success;
    }

    public Program getProgram() {
        return program;
    }

    public boolean isSuccess() {
        return success;
    }
}

public class SoundBMC implements Callable<SMTReturnCode> {

    private Program program;

    private DebugUtil debugUtil;

    public SoundBMC(Program program, DebugUtil debugUtil) {
        this.program = program;
        this.debugUtil = debugUtil;
    }

    private TransformationResult applyShadowVisitor(Map<Node, Node> predMap, Program program) {
        program = (Program) new ShadowVisitor(predMap, program).visit(program);
        program = (Program) new DefaultVisitor(predMap).visit(program);

        return new TransformationResult(program, !Thread.currentThread().isInterrupted());
    }

    private boolean applyMethodSummarisation(Map<Node, Node> predMap) {
        program = (Program) new MethodSummarisationVisitor(predMap, program).visit(program);
        debugUtil.print("Code after method summarisation is applied:\n" +
                new PrintVisitor().visit(program));
        return Thread.currentThread().isInterrupted();
    }

    // For every loop, set how much it should be unwind
    private boolean initialiseUnwindingOfEachLoop(
            Queue<ProcedureDecl> toRecompute,
            Map<WhileStmt, Integer> currUnwind) {
        for (ProcedureDecl procedureDecl : program.getProcedureDecls()) {
            toRecompute.add(procedureDecl);
            for (WhileStmt loop : procedureDecl.getLoops()) {
                currUnwind.put(loop, 0);
            }
        }
        return Thread.currentThread().isInterrupted();
    }

    // Check if the program is incorrect for a legitimate condition
    private SMTReturnCode checkReasonForIncorrect(Map<Node, Node> predMap,
                                                  SMTResult result,
                                                  Set<Node> criticalFailures,
                                                  Set<Node> failedNodes) {
        for (Node failure : criticalFailures) {
            if (failedNodes.contains(failure)) {
                return SMTReturnCode.INCORRECT;
            }
        }
        return Thread.currentThread().isInterrupted() ? SMTReturnCode.UNKNOWN :
                SMTReturnCode.CORRECT;
    }

    private SMTReturnCode verifySoundBMC(Map<Node, Node> predMap,
                                         Set<Node> criticalFailures,
                                         Program program,
                                         String methodName,
                                         BMCVisitor bmcVisitor,
                                         Map<WhileStmt, Integer> currUnwind) {
        // apply variable shadow removal
        TransformationResult firstPassResult = applyShadowVisitor(predMap, program);
        if (!firstPassResult.isSuccess()) {
            return SMTReturnCode.UNKNOWN;
        }
        program = firstPassResult.getProgram();

        MethodVerifier methodVerifier = new MethodVerifier(predMap, program, debugUtil);
        for (ProcedureDecl proc : program.getProcedureDecls()) {
            // not the smartest way to find the method in question; but OK for now
            if (proc.getMethodName().equals(methodName)) {
                // Verify method using Z3
                SMTResult result;
                try {
                    result = methodVerifier.verifyMethod(proc);
                } catch (Exception exception) {
                    return SMTReturnCode.UNKNOWN;
                }
                if (result.getReturnCode() == SMTReturnCode.UNKNOWN) {
                    return SMTReturnCode.UNKNOWN;
                }
                Set<Node> failedNodes = SmtUtil.getAllFailedNodes(predMap, result);
                SMTReturnCode code = checkReasonForIncorrect(predMap,
                        result,
                        criticalFailures,
                        failedNodes);
                if (code != SMTReturnCode.CORRECT) {
                    return code;
                }
                Map<AssertStmt, WhileStmt> stopConditionsForLoops = bmcVisitor.getStopAsserts();
                boolean hasToRecompute = false;
                for (Map.Entry<AssertStmt, WhileStmt> loopEntry : stopConditionsForLoops.entrySet()) {
                    if (failedNodes.contains(loopEntry.getKey())) {
                        // it means we've never reached the end of that while loop ; update
                        WhileStmt whileStmt = loopEntry.getValue();
                        currUnwind.put(whileStmt, currUnwind.get(whileStmt) + 1);
                        hasToRecompute = true;
                    }
                }
                if (!hasToRecompute) {
                    return SMTReturnCode.CORRECT;
                }
            }
        }
        return Thread.currentThread().isInterrupted() ? SMTReturnCode.UNKNOWN :
                SMTReturnCode.MAYBE_COREECT;
    }

    // This strategy uses sound BMC for loops. It attempts to prove the program is correct
    @Override
    public SMTReturnCode call() {
        Map<Node, Node> predMap = new HashMap<>();

        if (applyMethodSummarisation(predMap)) {
            return SMTReturnCode.UNKNOWN;
        }
        Queue<ProcedureDecl> toRecompute = new LinkedList<>();
        Map<WhileStmt, Integer> currUnwind = new HashMap<>();
        if (initialiseUnwindingOfEachLoop(toRecompute, currUnwind)) {
            return SMTReturnCode.UNKNOWN;
        }

        while (!toRecompute.isEmpty()) {
            ProcedureDecl procedureDecl = toRecompute.remove();
            Set<Node> criticalFailures = procedureDecl.getPotentiallyCriticalFailures();
            debugUtil.print(String.format("Analyzing procedure: %s\n", procedureDecl.getMethodName()));
            // analyze this procedure and put it back in the queue if required

            BMCVisitor bmcVisitor = new BMCVisitor(predMap, currUnwind, BmcType.SOUND_PROBE);
            SMTReturnCode returnCode = applyBMC(predMap, currUnwind, procedureDecl, criticalFailures, bmcVisitor);
            if (returnCode != SMTReturnCode.CORRECT) {
                return returnCode;
            }

            bmcVisitor = new BMCVisitor(predMap, currUnwind, BmcType.SOUND);
            returnCode = applyBMC(predMap, currUnwind, procedureDecl, criticalFailures, bmcVisitor);
            if (returnCode == SMTReturnCode.INCORRECT || returnCode == SMTReturnCode.UNKNOWN) {
                return returnCode;
            } else if (returnCode == SMTReturnCode.MAYBE_COREECT) {
                // put it back if no errors were detected, nor is the loop completely unwind
                toRecompute.add(procedureDecl);
            }
        }
        return SMTReturnCode.CORRECT;
    }

    private SMTReturnCode applyBMC(Map<Node, Node> predMap,
                                   Map<WhileStmt, Integer> currUnwind,
                                   ProcedureDecl procedureDecl,
                                   Set<Node> criticalFailures,
                                   BMCVisitor bmcVisitor) {
        ProcedureDecl transformedProcedure = (ProcedureDecl) bmcVisitor.visit(procedureDecl);

        // Program with this corresponding method replaced
        Program modifiedProgram =
                (Program) new MethodReplaceVisitor(predMap, transformedProcedure).
                        visit(program);

        return verifySoundBMC(predMap,
                criticalFailures,
                modifiedProgram,
                procedureDecl.getMethodName(),
                bmcVisitor,
                currUnwind);
    }
}
