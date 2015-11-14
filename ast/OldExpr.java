package ast;

import ast.visitor.Visitor;

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
}
