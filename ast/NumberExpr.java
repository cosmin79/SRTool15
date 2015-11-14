package ast;

import ast.visitor.Visitor;

public class NumberExpr extends AtomExpr {

    private Integer number;

    public NumberExpr(Integer number) {
        this.number = number;
    }

    public Integer getNumber() {
        return number;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
