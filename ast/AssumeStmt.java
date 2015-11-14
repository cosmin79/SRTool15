package ast;

import ast.visitor.Visitor;

public class AssumeStmt extends Stmt {

    private Expr condition;

    public AssumeStmt(Expr condition) {
        this.condition = condition;
    }

    public Expr getCondition() {
        return condition;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
