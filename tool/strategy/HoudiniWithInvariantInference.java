package tool.strategy;

import ast.Program;
import ast.visitor.impl.DefaultVisitor;
import ast.visitor.impl.InvariantGenVisitor;
import ast.visitor.impl.PrintVisitor;
import ast.visitor.impl.ShadowVisitor;
import tool.DebugUtil;

import java.util.HashMap;

public class HoudiniWithInvariantInference extends HoudiniWithLoopSummary {

    public HoudiniWithInvariantInference(Program program, DebugUtil debugUtil, String testPath) {
        super(program, debugUtil, testPath);
        program = (Program) new InvariantGenVisitor(new HashMap<>(), program).visit(program);
        program = (Program) new ShadowVisitor(new HashMap<>(), program).visit(program);
        this.program = (Program) new DefaultVisitor(new HashMap<>()).visit(program);
        this.strategyName = "houdiniInvariantInference";
        debugUtil.print("Program after loop invariant generation visitor:\n" + new PrintVisitor().visit(this.program));
    }
}
