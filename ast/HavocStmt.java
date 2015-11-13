package ast;

public class HavocStmt extends Stmt {

    private VarRef var;

    public HavocStmt(VarRef var) {
        this.var = var;
    }

    public VarRef getVar() {
        return var;
    }
}
