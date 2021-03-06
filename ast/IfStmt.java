package ast;

import ast.visitor.Visitor;

public class IfStmt extends Stmt {

    private Expr condition;

    private BlockStmt thenBlock;

    private BlockStmt elseBlock;

    public IfStmt(Expr condition, BlockStmt thenBlock, BlockStmt elseBlock) {
        this.condition = condition;
        this.thenBlock = thenBlock;
        this.elseBlock = elseBlock;
        addModSet(thenBlock);
        addModSet(elseBlock);
        addPotentialFailures(thenBlock);
        addPotentialFailures(elseBlock);
        addLoops(thenBlock);
        addLoops(elseBlock);
        addCalls(thenBlock);
        addCalls(elseBlock);
        addAssumes(thenBlock);
        addAssumes(elseBlock);
    }

    public Expr getCondition() {
        return condition;
    }

    public BlockStmt getThenBlock() {
        return thenBlock;
    }

    public BlockStmt getElseBlock() {
        return elseBlock;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
