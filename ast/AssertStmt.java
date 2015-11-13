package ast;

public class AssertStmt extends Stmt {

    private Expr condition;

    public AssertStmt(Expr condition) {
        this.condition = condition;
    }

    public Expr getCondition() {
        return condition;
    }
}
