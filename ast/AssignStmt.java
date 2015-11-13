package ast;

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
}
