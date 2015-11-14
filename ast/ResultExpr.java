package ast;

import ast.visitor.Visitor;

public class ResultExpr extends AtomExpr {

    public ResultExpr() { }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
