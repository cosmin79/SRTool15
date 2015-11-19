package ast;

import ast.visitor.Visitor;

public class Invariant extends LoopInvariant {

    private Expr condition;

    public Invariant(Expr condition) {
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
