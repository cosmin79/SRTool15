package ast;

import ast.visitor.Visitor;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

public class OldExpr extends AtomExpr {

    private VarRef var;

    public OldExpr(VarRef var) {
        this.var = var;
    }

    public VarRef getVar() {
        return var;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }

    @Override
    public Set<String> getRefVars() {
        Set<String> result = new HashSet<>();
        result.add(var.getVarIdentifier().getVarName());

        return result;
    }

    @Override
    public Boolean isCandidateHoudini() {
        return true;
    }

    @Override
    public List<Expr> getExprs() {
        return new LinkedList<>();
    }
}
