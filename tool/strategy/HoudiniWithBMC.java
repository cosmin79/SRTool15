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

public class HoudiniWithBMC implements Callable<SMTReturnCode> {

    private Program program;

    private DebugUtil debugUtil;

    private Set<Node> consideredCandidates;

    public HoudiniWithBMC(Program program, DebugUtil debugUtil) {
        this.program = program;
        this.debugUtil = debugUtil;
        consideredCandidates = new HashSet<>();
    }

    private TransformationResult applyShadowVisitor(Map<Node, Node> predMap, Program program) {
        program = (Program) new ShadowVisitor(predMap, program).visit(program);
        program = (Program) new DefaultVisitor(predMap).visit(program);

        return new TransformationResult(program, !Thread.currentThread().isInterrupted());
    }

    private boolean addCandidatePrePostConditions() {
        for (ProcedureDecl procedureDecl : program.getProcedureDecls()) {
            for (PrePostCondition prePostCondition : procedureDecl.getPrePostConditions()) {
                if ((prePostCondition instanceof CandidatePrecondition) ||
                        (prePostCondition instanceof CandidatePostcondition)) {
                    consideredCandidates.add(prePostCondition);
                }
            }
        }
        return Thread.currentThread().isInterrupted();
    }

    private TransformationResult applyMethodSummarisation(Map<Node, Node> predMap, Program program) {
        program = (Program) new MethodSummarisationVisitor(predMap, program).visit(program);
        debugUtil.print("Code after method summarisation is applied:\n" +
                new PrintVisitor().visit(program));

        return new TransformationResult(program, !Thread.currentThread().isInterrupted());
    }

    // For every loop, set how much it should be unwind
    private boolean initialiseUnwindingOfEachLoop(
            Program program,
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
    private SMTReturnCode checkReasonForIncorrect(Set<Node> criticalFailures,
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
        TransformationResult shadowVisitorResult = applyShadowVisitor(predMap, program);
        if (!shadowVisitorResult.isSuccess()) {
            return SMTReturnCode.UNKNOWN;
        }
        program = shadowVisitorResult.getProgram();

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

                // make sure no critical assert (assert, precond, postcond, invariant) occurred
                SMTReturnCode code = checkReasonForIncorrect(criticalFailures, failedNodes);
                if (code != SMTReturnCode.CORRECT) {
                    return code;
                }

                // inspect whether any of the houdini candidates failed
                Set<Node> failedCandidates = new HashSet<>();
                for (Node candidate: consideredCandidates) {
                    if (failedNodes.contains(candidate)) {
                        failedCandidates.add(candidate);
                    }
                }
                if (!failedCandidates.isEmpty()) {
                    consideredCandidates.removeAll(failedCandidates);
                    return SMTReturnCode.FAILED_CANDIDATE_HOUDINI;
                }

                // if we got here it means that we might have failed a loop "stop" assert
                Map<AssertStmt, WhileStmt> stopConditionsForLoops = bmcVisitor.getStopAsserts();
                boolean hasToRecompute = false;
                for (Map.Entry<AssertStmt, WhileStmt> loopEntry : stopConditionsForLoops.entrySet()) {
                    if (failedNodes.contains(loopEntry.getKey())) {
                        // it means we've never reached the end of that while loop ; update
                        WhileStmt whileStmt = loopEntry.getValue();
                        currUnwind.put(whileStmt, currUnwind.get(whileStmt) + 2);
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
        TransformationResult shadowVisitorResult = applyShadowVisitor(predMap, program);
        if (!shadowVisitorResult.isSuccess()) {
            return SMTReturnCode.UNKNOWN;
        }
        program = shadowVisitorResult.getProgram();
        Set<Node> criticalFailures = program.getPotentiallyCriticalFailures();

        if (addCandidatePrePostConditions()) {
            return SMTReturnCode.UNKNOWN;
        }

        Boolean updateHoudini = true;
        while (updateHoudini) {
            updateHoudini = false;
            Program intermediateProgram =
                    (Program) new HoudiniVisitor(predMap, consideredCandidates).
                            visit(program);
            debugUtil.print("Program being considered in this HoudiniWithLoopSummary iteration:\n" +
                    new PrintVisitor().visit(intermediateProgram));

            TransformationResult methodSummaryResult = applyMethodSummarisation(predMap, intermediateProgram);
            if (!methodSummaryResult.isSuccess()) {
                return SMTReturnCode.UNKNOWN;
            }
            intermediateProgram = methodSummaryResult.getProgram();

            Queue<ProcedureDecl> toRecompute = new LinkedList<>();
            Map<WhileStmt, Integer> currUnwind = new HashMap<>();
            if (initialiseUnwindingOfEachLoop(intermediateProgram, toRecompute, currUnwind)) {
                return SMTReturnCode.UNKNOWN;
            }

            while (!toRecompute.isEmpty()) {
                ProcedureDecl procedureDecl = toRecompute.remove();
                debugUtil.print(String.format("Analyzing procedure: %s\n", procedureDecl.getMethodName()));
                // analyze this procedure and put it back in the queue if required

                BMCVisitor bmcVisitor = new BMCVisitor(predMap, currUnwind);
                ProcedureDecl transformedProcedure = (ProcedureDecl) bmcVisitor.visit(procedureDecl);
                debugUtil.print("Code after loop unwinding is applied:\n" +
                        new PrintVisitor().visit(transformedProcedure));

                // Program with this corresponding method replaced
                Program modifiedProgram =
                        (Program) new MethodReplaceVisitor(predMap, transformedProcedure).
                                visit(intermediateProgram);

                SMTReturnCode returnCode = verifySoundBMC(predMap,
                        criticalFailures,
                        modifiedProgram,
                        procedureDecl.getMethodName(),
                        bmcVisitor,
                        currUnwind);
                if (returnCode == SMTReturnCode.INCORRECT || returnCode == SMTReturnCode.UNKNOWN) {
                    return returnCode;
                } else if (returnCode == SMTReturnCode.FAILED_CANDIDATE_HOUDINI) {
                    // we've already updated the candidate pre-post conditions ; start again
                    updateHoudini = true;
                    break ;
                } else if (returnCode == SMTReturnCode.MAYBE_COREECT) {
                    // put it back if no errors were detected, nor is the loop completely unwind
                    toRecompute.add(procedureDecl);
                }
            }
        }

        return SMTReturnCode.CORRECT;
    }
}
