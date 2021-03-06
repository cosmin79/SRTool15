package ast;

import ast.visitor.Visitor;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

public class ResultExpr extends AtomExpr {

    public ResultExpr() { }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }

    @Override
    public Set<String> getRefVars() {
        return new HashSet<>();
    }

    @Override
    public Boolean isCandidateHoudini() {
        return false;
    }

    @Override
    public List<Expr> getExprs() {
        return new LinkedList<>();
    }
}
