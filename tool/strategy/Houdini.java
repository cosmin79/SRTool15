package tool.strategy;

import ast.*;
import ast.visitor.impl.*;
import tool.*;

import java.io.IOException;
import java.util.*;

public class Houdini {

    private Program program;

    private DebugUtil debugUtil;

    // Those are candidate preconditions, postconditions and loop invariants
    private Set<Node> consideredCandidates;

    public Houdini(Program program, DebugUtil debugUtil) {
        this.program = program;
        this.debugUtil = debugUtil;
        consideredCandidates = new HashSet<>();
    }

    public SMTReturnCode run() throws IOException, InterruptedException {
        Map<Node, Node> predMap = new HashMap<>();
        program = (Program) new ShadowVisitor(predMap, program).visit(program);
        program = (Program) new DefaultVisitor(predMap).visit(program);
        Set<Node> criticalFailures = program.getPotentiallyCriticalFailures();

        // add all candidate preconditions and postconditions
        for (ProcedureDecl procedureDecl: program.getProcedureDecls()) {
            for (PrePostCondition prePostCondition: procedureDecl.getPrePostConditions()) {
                if ((prePostCondition instanceof CandidatePrecondition) ||
                        (prePostCondition instanceof CandidatePostcondition)) {
                    consideredCandidates.add(prePostCondition);
                }
            }
        }

        // add all candidate invariants
        for (WhileStmt whileStmt: program.getLoops()) {
            for (LoopInvariant loopInvariant: whileStmt.getLoopInvariantList()) {
                if (loopInvariant instanceof CandidateInvariant) {
                    consideredCandidates.add(loopInvariant);
                }
            }
        }

        debugUtil.print("Starting analyzing with Houdini\n");
        Boolean updateHoudini = true;
        while (updateHoudini) {
            Program intermediateProgram = (Program) new HoudiniVisitor(predMap, consideredCandidates).visit(program);
            debugUtil.print("Program being considered in this Houdini iteration:\n" + new PrintVisitor().visit(intermediateProgram));
            intermediateProgram
                    = (Program) new MethodSummarisationVisitor(predMap, intermediateProgram).visit(intermediateProgram);
            debugUtil.print("Code after method summarisation is applied:\n" + new PrintVisitor().visit(intermediateProgram));

            intermediateProgram = (Program) new LoopSummarisationVisitor(predMap).visit(intermediateProgram);
            debugUtil.print("Code after loop summarisation is applied:\n" + new PrintVisitor().visit(intermediateProgram));

            MethodVerifier methodVerifier = new MethodVerifier(predMap, intermediateProgram, debugUtil);

            updateHoudini = false;
            for(ProcedureDecl proc: intermediateProgram.getProcedureDecls()) {
                SMTResult result = methodVerifier.verifyMethod(proc);

                if (result.getReturnCode() == SMTReturnCode.UNKNOWN) {
                    debugUtil.print("Some error occurred while verifying " + proc.getMethodName());
                    return SMTReturnCode.UNKNOWN;
                } else if (result.getReturnCode() == SMTReturnCode.INCORRECT) {
                    // check if the program is incorrect because of a legitimate condition
                    Set<Node> failedNodes = SmtUtil.getAllFailedNodes(predMap, result);
                    for (Node failure: criticalFailures) {
                        if (failedNodes.contains(failure)) {
                            return SMTReturnCode.INCORRECT;
                        }
                    }

                    // update set of candidates
                    Set<Node> newCandidates = new HashSet<>();
                    for (Node candidate: consideredCandidates) {
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
