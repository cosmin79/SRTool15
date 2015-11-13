package ast;

public class VarRefExpr extends AtomExpr {

    private VarRef varRef;

    public VarRefExpr(VarRef varRef) {
        this.varRef = varRef;
    }

    public VarRef getVarRef() {
        return varRef;
    }
}
