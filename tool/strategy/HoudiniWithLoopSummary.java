package tool.strategy;

import ast.*;
import ast.visitor.impl.*;
import tool.*;

import java.io.IOException;
import java.util.*;

import java.util.concurrent.Callable;

public class HoudiniWithLoopSummary implements Callable<SMTReturnCode> {

    protected Program program;

    private DebugUtil debugUtil;

    // Those are candidate preconditions, postconditions and loop invariants
    private Set<Node> consideredCandidates;

    public HoudiniWithLoopSummary(Program program, DebugUtil debugUtil) {
        this.program = program;
        this.debugUtil = debugUtil;
        consideredCandidates = new HashSet<>();
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

    private boolean addCandidateInvariants() {
        for (WhileStmt whileStmt : program.getLoops()) {
            for (LoopInvariant loopInvariant : whileStmt.getLoopInvariantList()) {
                if (loopInvariant instanceof CandidateInvariant) {
                  consideredCandidates.add(loopInvariant);
                }
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

    @Override
    public SMTReturnCode call() {
        Map<Node, Node> predMap = new HashMap<>();
        Set<Node> criticalFailures = program.getPotentiallyCriticalFailures();
        if (addCandidatePrePostConditions()) {
            return SMTReturnCode.UNKNOWN;
        }
        if (addCandidateInvariants()) {
            return SMTReturnCode.UNKNOWN;
        }

        debugUtil.print("Starting analyzing with HoudiniWithLoopSummary\n");
        Boolean updateHoudini = true;
        while (updateHoudini) {
            Program intermediateProgram =
                    (Program) new HoudiniVisitor(predMap, consideredCandidates).
                            visit(program);
            debugUtil.print("Program being considered in this HoudiniWithLoopSummary iteration:\n" +
                    new PrintVisitor().visit(intermediateProgram));
            intermediateProgram =
                    (Program) new MethodSummarisationVisitor(predMap, intermediateProgram).
                            visit(intermediateProgram);
            debugUtil.print("Code after method summarisation is applied:\n" +
                    new PrintVisitor().visit(intermediateProgram));
            intermediateProgram =
                    (Program) new LoopSummarisationVisitor(predMap).
                            visit(intermediateProgram);
            debugUtil.print("Code after loop summarisation is applied:\n" +
                    new PrintVisitor().visit(intermediateProgram));

            MethodVerifier methodVerifier = new MethodVerifier(predMap,
                    intermediateProgram,
                    debugUtil);
            updateHoudini = false;
            for (ProcedureDecl proc : intermediateProgram.getProcedureDecls()) {
                SMTResult result;
                try {
                    result = methodVerifier.verifyMethod(proc);
                } catch (Exception exception) {
                    return SMTReturnCode.UNKNOWN;
                }
                if (result.getReturnCode() == SMTReturnCode.UNKNOWN) {
                    debugUtil.print("Some error occurred while verifying " + proc.getMethodName());
                    return SMTReturnCode.UNKNOWN;
                } else if (result.getReturnCode() == SMTReturnCode.INCORRECT) {
                    // check if the program is incorrect because of a legitimate condition
                    Set<Node> failedNodes = SmtUtil.getAllFailedNodes(predMap, result);
                    SMTReturnCode code = checkReasonForIncorrect(predMap,
                            result,
                            criticalFailures,
                            failedNodes);
                    if (code != SMTReturnCode.CORRECT) {
                        return code;
                    }

                    // update set of candidates
                    Set<Node> newCandidates = new HashSet<>();
                    for (Node candidate : consideredCandidates) {
                        if (!failedNodes.contains(candidate)) {
                            newCandidates.add(candidate);
                        } else {
                            updateHoudini = true;
                        }
                    }
                    consideredCandidates = newCandidates;
                }
            }
        }

        return SMTReturnCode.CORRECT;
    }
}
