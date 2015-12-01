package ast;

import ast.visitor.Visitor;

import java.util.LinkedList;
import java.util.List;
import java.util.Set;

public class ParenExpr extends AtomExpr {

    private Expr expr;

    public ParenExpr(Expr expr) {
        this.expr = expr;
    }

    public Expr getExpr() {
        return expr;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }

    @Override
    public Set<String> getRefVars() {
        return expr.getRefVars();
    }

    // We will capture the underlying expression anyway
    @Override
    public Boolean isCandidateHoudini() {
        return false;
    }

    @Override
    public List<Expr> getExprs() {
        return expr.getExprs();
    }
}
