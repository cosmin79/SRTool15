package ast;

import ast.visitor.Visitor;

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
}
