package ast;

import ast.visitor.Visitor;

public class UnaryExpr extends Expr {

    private String unaryOp;

    private Expr arg;

    public UnaryExpr(String unaryOp, Expr arg) {
        this.unaryOp = unaryOp;
        this.arg = arg;
    }

    public String getUnaryOp() {
        return unaryOp;
    }

    public Expr getArg() {
        return arg;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
