package ast;

public class BinaryExpr extends Expr {

    private String binaryOp;

    private Expr lhs;

    private Expr rhs;

    public BinaryExpr(String binaryOp, Expr lhs, Expr rhs) {
        this.binaryOp = binaryOp;
        this.lhs = lhs;
        this.rhs = rhs;
    }

    public String getBinaryOp() {
        return binaryOp;
    }

    public Expr getLhs() {
        return lhs;
    }

    public Expr getRhs() {
        return rhs;
    }
}
