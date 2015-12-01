package ast;

import ast.visitor.Visitor;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

public class VarRefExpr extends AtomExpr {

    private VarRef varRef;

    public VarRefExpr(VarRef varRef) {
        this.varRef = varRef;
    }

    public VarRef getVarRef() {
        return varRef;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }

    @Override
    public Set<String> getRefVars() {
        Set<String> result = new HashSet<>();
        result.add(varRef.getVarIdentifier().getVarName());
        return result;
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
