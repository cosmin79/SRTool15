package ast;

public class VarIdentifier extends Node {

    private String varName;

    public VarIdentifier(String varName) {
        this.varName = varName;
    }

    public String getVarName() {
        return varName;
    }
}
