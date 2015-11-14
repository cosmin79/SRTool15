package ast;

import ast.visitor.Visitor;

public class FormalParam extends Node {

    private VarIdentifier varIdentifier;

    public FormalParam(VarIdentifier varIdentifier) {
        this.varIdentifier = varIdentifier;
    }

    public VarIdentifier getVarIdentifier() {
        return varIdentifier;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
