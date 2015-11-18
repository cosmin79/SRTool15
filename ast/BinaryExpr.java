package ast;

import ast.visitor.Visitor;

import java.util.LinkedList;
import java.util.List;

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

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
