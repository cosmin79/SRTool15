package tool.strategy;

import ast.Node;
import ast.ProcedureDecl;
import ast.Program;
import ast.visitor.impl.*;
import tool.DebugUtil;
import tool.MethodVerifier;
import tool.SMTResult;
import tool.SMTReturnCode;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

public class UnsoundBMC {

    private final static Integer MAX_UNWIND = 20;

    private Program program;

    private DebugUtil debugUtil;

    public UnsoundBMC(Program program, DebugUtil debugUtil) {
        this.program = program;
        this.debugUtil = debugUtil;
    }

    // This strategy uses unsound BMC for loops. It attempts to prove the program is incorrect
    // It may give false positives. No false negatives though!
    public SMTReturnCode run() throws IOException, InterruptedException {
        Map<Node, Node> predMap = new HashMap<>();
        program = (Program) new ShadowVisitor(predMap, program).visit(program);
        program = (Program) new DefaultVisitor(predMap).visit(program);

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
}
