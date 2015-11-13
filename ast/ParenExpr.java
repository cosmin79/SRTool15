package ast;

public class ParenExpr extends AtomExpr {

    private Expr expr;

    public ParenExpr(Expr expr) {
        this.expr = expr;
    }

    public Expr getExpr() {
        return expr;
    }
}
