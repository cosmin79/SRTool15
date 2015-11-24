package ast;

import ast.visitor.Visitor;

import java.util.HashSet;
import java.util.Set;

public class NumberExpr extends AtomExpr {

    public static final NumberExpr TRUE = new NumberExpr(1);

    public static final NumberExpr FALSE = new NumberExpr(0);

    private Integer number;

    public NumberExpr(Integer number) {
        this.number = number;
    }

    public Integer getNumber() {
        return number;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }

    @Override
    public int hashCode() {
        return number;
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
}
