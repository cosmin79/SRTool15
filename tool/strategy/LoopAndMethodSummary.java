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

public class LoopAndMethodSummary {

    private Program program;

    private DebugUtil debugUtil;

    public LoopAndMethodSummary(Program program, DebugUtil debugUtil) {
        this.program = program;
        this.debugUtil = debugUtil;
    }

    // This strategy uses loop and method summarisation. It attempts to prove the program is correct
    // It may give false negatives. No false positives though!
    public SMTReturnCode run() throws IOException, InterruptedException {
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
}
