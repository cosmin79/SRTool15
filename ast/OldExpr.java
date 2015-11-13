package ast;

public class OldExpr extends AtomExpr {

    private VarRef var;

    public OldExpr(VarRef var) {
        this.var = var;
    }

    public VarRef getVar() {
        return var;
    }
}
