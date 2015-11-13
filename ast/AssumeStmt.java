package ast;

public class AssumeStmt extends Stmt {

    private Expr condition;

    public AssumeStmt(Expr condition) {
        this.condition = condition;
    }

    public Expr getCondition() {
        return condition;
    }
}
