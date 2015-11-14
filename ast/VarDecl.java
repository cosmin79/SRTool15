package ast;

import ast.visitor.Visitor;

public class VarDecl extends Stmt {

    private VarIdentifier varIdentifier;

    public VarDecl(VarIdentifier varIdentifier) {
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
