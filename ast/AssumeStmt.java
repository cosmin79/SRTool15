package ast;

import ast.visitor.Visitor;

import java.util.LinkedList;
import java.util.List;

public class AssumeStmt extends Stmt {

    private Expr condition;

    public AssumeStmt(Expr condition) {
        this.condition = condition;
        addAssume(this);
    }

    public Expr getCondition() {
        return condition;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
