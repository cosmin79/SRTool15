package ast;

import ast.visitor.Visitor;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

public class NumberExpr extends AtomExpr {

    public static final NumberExpr TRUE = new NumberExpr(Long.valueOf(1));

    public static final NumberExpr FALSE = new NumberExpr(Long.valueOf(0));

    private Long number;

    public NumberExpr(Long number) {
        this.number = number;
    }

    public Long getNumber() {
        return number;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }

    @Override
    public int hashCode() {
        return number.hashCode();
    }

    @Override
    public boolean equals(Object other) {
        if (!(other instanceof NumberExpr)) {
            return false;
        }
        NumberExpr otherNumber = (NumberExpr) other;

        return number == otherNumber.number;
    }

    @Override
    public Set<String> getRefVars() {
        return new HashSet<>();
    }

    @Override
    public Boolean isCandidateHoudini() {
        return true;
    }

    @Override
    public List<Expr> getExprs() {
        List<Expr> underlyingExprs = new LinkedList<>();
        underlyingExprs.add(this);

        return underlyingExprs;
    }
}
