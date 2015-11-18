package tool;

import ast.*;
import ast.visitor.impl.*;

import java.io.IOException;
import java.util.*;

public class ExecutionPlan {

    private final static Integer MAX_UNWIND = 20;

    private DebugUtil debugUtil;

    private final Program program;

    public ExecutionPlan(Program program, DebugUtil debugUtil) {
        this.program = program;
        this.debugUtil = debugUtil;
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

    public void verifyProgram() throws IOException, InterruptedException {
        // apply strategy 1
        SMTReturnCode returnCode = strategy1(cloneProgram());
        if (returnCode != SMTReturnCode.INCORRECT) {
            decide(returnCode);
        } else {
            returnCode = strategy2(cloneProgram());
            // note that strategy 2 is looking for bugs ; if it finds one => STOP!
            if (returnCode != SMTReturnCode.CORRECT) {
                decide(returnCode);
            } else {
                // this applied sound BMC. We need a timeout version though as it might not terminate...
                returnCode = strategy3(cloneProgram());
                decide(returnCode);
                // By the way, in this strategy we might loop forever :D
            }
        }
    }

    // This strategy uses loop and method summarisation. It attempts to prove the program is correct
    // It may give false negatives. No false positives though!
    public SMTReturnCode strategy1(Program program) throws IOException, InterruptedException {
        Map<Node, Node> predMap = new HashMap<>();

        // apply variable shadow removal
        program = (Program) new ShadowVisitor(predMap, program).visit(program);
        debugUtil.print("Code after shadow visiting is applied:\n" + new PrintVisitor().visit(program));

        // apply method summarisation (when calls occur) ; calling default visitor once to populate modSet
        program = (Program) new DefaultVisitor(predMap).visit(program);
        program = (Program) new MethodSummarisationVisitor(predMap, program).visit(program);
        debugUtil.print("Code after method summarisation is applied:\n" + new PrintVisitor().visit(program));

        // apply loop summarisation
        program = (Program) new LoopSummarisationVisitor(predMap).visit(program);
        debugUtil.print("Code after loop summarisation is applied:\n" + new PrintVisitor().visit(program));

        MethodVerifier methodVerifier = new MethodVerifier(predMap, program, debugUtil);
        for(ProcedureDecl proc: program.getProcedureDecls()) {
            SMTResult result = methodVerifier.verifyMethod(proc);

            if (result.getReturnCode() != SMTReturnCode.CORRECT) {
                return result.getReturnCode();
            }
        }

        return SMTReturnCode.CORRECT;
    }

    // This strategy uses unsound BMC for loops. It attempts to prove the program is incorrect
    // It may give false positives. No false negatives though!
    public SMTReturnCode strategy2(Program program) throws IOException, InterruptedException {
        Map<Node, Node> predMap = new HashMap<>();

        // apply method summarisation (when calls occur)
        program = (Program) new MethodSummarisationVisitor(predMap, program).visit(program);
        debugUtil.print("Code after method summarisation is applied:\n" + new PrintVisitor().visit(program));

        // apply loop unwdining: unsound BMC
        program = (Program) new BMCVisitor(predMap, MAX_UNWIND).visit(program);
        debugUtil.print("Code after loop unwinding is applied:\n" + new PrintVisitor().visit(program));

        // apply variable shadow removal
        program = (Program) new ShadowVisitor(predMap, program).visit(program);

        debugUtil.print("Code after shadow visiting is applied:\n" + new PrintVisitor().visit(program));

        MethodVerifier methodVerifier = new MethodVerifier(predMap, program, debugUtil);
        for(ProcedureDecl proc: program.getProcedureDecls()) {
            SMTResult result = methodVerifier.verifyMethod(proc);

            if (result.getReturnCode() != SMTReturnCode.CORRECT) {
                return result.getReturnCode();
            }
        }

        return SMTReturnCode.CORRECT;
    }

    private Set<Node> getAllFailedNodes(Map<Node, Node> predMap, SMTResult smtResult) {
        Set<Node> result = new HashSet<>();
        Iterator<AssertStmt> assertStmtIterator = smtResult.getFailedAsserts().iterator();
        while (assertStmtIterator.hasNext()) {
            Node stmt = assertStmtIterator.next();
            while (stmt != null) {
                result.add(stmt);
                stmt = predMap.get(stmt);
            }
        }

        return result;
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
                Set<Node> failedNodes = getAllFailedNodes(predMap, result);
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
    public SMTReturnCode strategy3(Program program) throws IOException, InterruptedException {
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
