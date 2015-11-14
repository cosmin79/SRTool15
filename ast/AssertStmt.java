package ast;

import ast.visitor.Visitor;

public class AssertStmt extends Stmt {

    private Expr condition;

    public AssertStmt(Expr condition) {
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
