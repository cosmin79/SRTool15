package ast;

public class FormalParam extends Node {

    private VarIdentifier varIdentifier;

    public FormalParam(VarIdentifier varIdentifier) {
        this.varIdentifier = varIdentifier;
    }

    public VarIdentifier getVarIdentifier() {
        return varIdentifier;
    }
}
