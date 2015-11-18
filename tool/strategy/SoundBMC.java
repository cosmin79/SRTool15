package tool.strategy;

import ast.*;
import ast.visitor.impl.*;
import tool.*;

import java.io.IOException;
import java.util.*;

public class SoundBMC {

    private Program program;

    private DebugUtil debugUtil;

    public SoundBMC(Program program, DebugUtil debugUtil) {
        this.program = program;
        this.debugUtil = debugUtil;
    }

    private SMTReturnCode verifySoundBMC(Map<Node, Node> predMap,
                                         Set<Node> criticalFailures,
                                         Program program,
                                         String methodName,
                                         BMCVisitor bmcVisitor,
                                         Map<WhileStmt, Integer> currUnwind) throws IOException, InterruptedException {
        // apply variable shadow removal
        program = (Program) new ShadowVisitor(predMap, program).visit(program);
        debugUtil.print("Code after shadow visiting is applied:\n" + new PrintVisitor().visit(program));

        MethodVerifier methodVerifier = new MethodVerifier(predMap, program, debugUtil);
        for (ProcedureDecl proc: program.getProcedureDecls()) {
            if (proc.getMethodName().equals(methodName)) {
                // not the smartest way to find the method in question ; but OK for now
                SMTResult result = methodVerifier.verifyMethod(proc);
                if (result.getReturnCode() == SMTReturnCode.UNKNOWN) {
                    return SMTReturnCode.UNKNOWN;
                }

                // check if the program is incorrect because of a legitimate condition
                Set<Node> failedNodes = SmtUtil.getAllFailedNodes(predMap, result);
                for (Node failure: criticalFailures) {
                    if (failedNodes.contains(failure)) {
                        return SMTReturnCode.INCORRECT;
                    }
                }

                Map<AssertStmt, WhileStmt> stopConditionsForLoops = bmcVisitor.getStopAsserts();
                boolean hasToRecompute = false;
                for (Map.Entry<AssertStmt, WhileStmt> loopEntry: stopConditionsForLoops.entrySet()) {
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

        return SMTReturnCode.MAYBE_COREECT;
    }

    // This strategy uses sound BMC for loops. It attempts to prove the program is correct
    public SMTReturnCode run() throws IOException, InterruptedException {
        Map<Node, Node> predMap = new HashMap<>();

        // apply method summarisation (when calls occur)
        program = (Program) new MethodSummarisationVisitor(predMap, program).visit(program);
        debugUtil.print("Code after method summarisation is applied:\n" + new PrintVisitor().visit(program));

        Queue<ProcedureDecl> toRecompute = new LinkedList<>();
        // For every loop, set how much it should be unwind
        Map<WhileStmt, Integer> currUnwind = new HashMap<>();
        for (ProcedureDecl procedureDecl: program.getProcedureDecls()) {
            toRecompute.add(procedureDecl);
            for (WhileStmt loop: procedureDecl.getLoops()) {
                currUnwind.put(loop, 0);
            }
        }

        while (!toRecompute.isEmpty()) {
            ProcedureDecl procedureDecl = toRecompute.remove();
            Set<Node> criticalFailures = procedureDecl.getPotentiallyCriticalFailures();
            debugUtil.print(String.format("Analyzing procedure: %s\n", procedureDecl.getMethodName()));
            // analyze this procedure and put it back in the queue if required

            BMCVisitor bmcVisitor = new BMCVisitor(predMap, currUnwind);
            ProcedureDecl transformedProcedure = (ProcedureDecl) bmcVisitor.visit(procedureDecl);
            debugUtil.print("Code after loop unwinding is applied:\n" + new PrintVisitor().visit(transformedProcedure));

            // Program with this corresponding method replaced
            Program modifiedProgram = (Program) new MethodReplaceVisitor(predMap, transformedProcedure).visit(program);

            SMTReturnCode returnCode
                    = verifySoundBMC(predMap, criticalFailures, modifiedProgram,
                    procedureDecl.getMethodName(), bmcVisitor, currUnwind);
            if (returnCode == SMTReturnCode.INCORRECT || returnCode == SMTReturnCode.UNKNOWN) {
                return returnCode;
            } else if (returnCode == SMTReturnCode.MAYBE_COREECT) {
                // put it back if no errors were detected, nor is the loop completely unwind
                toRecompute.add(procedureDecl);
            }
        }

        return SMTReturnCode.CORRECT;
    }
}
