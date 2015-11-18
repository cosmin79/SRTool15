package tool;

import ast.ProcedureDecl;
import ast.Program;
import ast.visitor.impl.*;

import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

public class ExecutionPlan {

    private final static Integer MAX_UNWIND = 20;

    private List<ProcedureDecl> toRecompute;

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
        return (Program) new DefaultVisitor().visit(program);
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
                // hopefully apply another strategy ?
                decide(SMTReturnCode.INCORRECT);
            }
        }
    }

    // This strategy uses loop and method summarisation
    public SMTReturnCode strategy1(Program program) throws IOException, InterruptedException {
        // apply variable shadow removal
        program = (Program) new ShadowVisitor(program).visit(program);
        debugUtil.print("Code after shadow visiting is applied:\n" + new PrintVisitor().visit(program));

        // apply method summarisation (when calls occur) ; calling default visitor once to populate modSet
        program = (Program) new DefaultVisitor().visit(program);
        program = (Program) new MethodSummarisationVisitor(program).visit(program);
        debugUtil.print("Code after method summarisation is applied:\n" + new PrintVisitor().visit(program));

        // apply loop summarisation
        program = (Program) new LoopSummarisationVisitor().visit(program);
        debugUtil.print("Code after loop summarisation is applied:\n" + new PrintVisitor().visit(program));

        MethodVerifier methodVerifier = new MethodVerifier(program, debugUtil);
        for(ProcedureDecl proc: program.getProcedureDecls()) {
            SMTResult result = methodVerifier.verifyMethod(proc);

            if (result.getReturnCode() != SMTReturnCode.CORRECT) {
                return result.getReturnCode();
            }
        }

        return SMTReturnCode.CORRECT;
    }

    // This strategy uses unsound BMC for loop
    public SMTReturnCode strategy2(Program program) throws IOException, InterruptedException {
        // apply method summarisation (when calls occur)
        program = (Program) new MethodSummarisationVisitor(program).visit(program);
        debugUtil.print("Code after method summarisation is applied:\n" + new PrintVisitor().visit(program));

        // apply loop unwdining: unsound BMC
        program = (Program) new BMCVisitor(false, MAX_UNWIND).visit(program);
        debugUtil.print("Code after loop unwinding is applied:\n" + new PrintVisitor().visit(program));

        // apply variable shadow removal
        program = (Program) new ShadowVisitor(program).visit(program);
        debugUtil.print("Code after shadow visiting is applied:\n" + new PrintVisitor().visit(program));

        MethodVerifier methodVerifier = new MethodVerifier(program, debugUtil);
        for(ProcedureDecl proc: program.getProcedureDecls()) {
            SMTResult result = methodVerifier.verifyMethod(proc);

            if (result.getReturnCode() != SMTReturnCode.CORRECT) {
                return result.getReturnCode();
            }
        }

        return SMTReturnCode.CORRECT;
    }
}
