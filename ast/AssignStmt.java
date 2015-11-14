package ast;

import ast.visitor.Visitor;

public class AssignStmt extends Stmt {

    private VarRef lhsVar;

    private Expr rhsExpr;

    public AssignStmt(VarRef lhsVar, Expr rhsExpr) {
        this.lhsVar = lhsVar;
        this.rhsExpr = rhsExpr;
    }

    public VarRef getLhsVar() {
        return lhsVar;
    }

    public Expr getRhsExpr() {
        return rhsExpr;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
