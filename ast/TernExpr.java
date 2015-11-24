package ast;

import ast.visitor.Visitor;

import java.util.HashSet;
import java.util.Set;

public class TernExpr extends Expr {

    private Expr condition;

    private Expr thenExpr;

    private Expr elseExpr;

    public TernExpr(Expr condition, Expr thenExpr, Expr elseExpr) {
        this.condition = condition;
        this.thenExpr = thenExpr;
        this.elseExpr = elseExpr;
    }

    public Expr getCondition() {
        return condition;
    }

    public Expr getThenExpr() {
        return thenExpr;
    }

    public Expr getElseExpr() {
        return elseExpr;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }

    @Override
    public Set<String> getRefVars() {
        Set<String> result = new HashSet<>();
        result.addAll(condition.getRefVars());
        result.addAll(thenExpr.getRefVars());
        result.addAll(elseExpr.getRefVars());

        return result;
    }

    @Override
    public Boolean isCandidateHoudini() {
        return false;
    }
}
