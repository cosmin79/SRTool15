package ast;

import ast.visitor.Visitor;

public class VarIdentifier extends Node {

    private String varName;

    public VarIdentifier(String varName) {
        this.varName = varName;
    }

    public String getVarName() {
        return varName;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
