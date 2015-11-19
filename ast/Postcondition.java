package ast;

import ast.visitor.Visitor;

public class Postcondition extends PrePostCondition {

    private Expr condition;

    public Postcondition(Expr condition) {
        this.condition = condition;
        addPotentialFailure(this);
    }

    public Expr getCondition() {
        return condition;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
