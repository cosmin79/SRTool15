package tool.strategy;

import ast.Program;
import ast.visitor.impl.InvariantGenVisitor;
import ast.visitor.impl.PrintVisitor;
import tool.DebugUtil;

import java.util.HashMap;

public class HoudiniWithInvariantInference extends HoudiniWithLoopSummary {

    public HoudiniWithInvariantInference(Program program, DebugUtil debugUtil) {
        super(program, debugUtil);
        this.program = (Program) new InvariantGenVisitor(new HashMap<>(), program).visit(program);
        debugUtil.print("Program after loop invariant generation visitor:\n" + new PrintVisitor().visit(this.program));
    }
}
