package ast;

import ast.visitor.Visitor;

public class HavocStmt extends Stmt {

    private VarRef var;

    public HavocStmt(VarRef var) {
        this.var = var;
    }

    public VarRef getVar() {
        return var;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
