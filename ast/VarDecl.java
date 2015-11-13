package ast;

public class VarDecl extends Stmt {

    private VarIdentifier varIdentifier;

    public VarDecl(VarIdentifier varIdentifier) {
        this.varIdentifier = varIdentifier;
    }

    public VarIdentifier getVarIdentifier() {
        return varIdentifier;
    }
}
