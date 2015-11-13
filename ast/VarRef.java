package ast;

public class VarRef extends Node {

    private VarIdentifier varIdentifier;

    public VarRef(VarIdentifier varIdentifier) {
        this.varIdentifier = varIdentifier;
    }

    public VarIdentifier getVarIdentifier() {
        return varIdentifier;
    }
}
