package ast;

import ast.visitor.Visitor;

public class Invariant extends LoopInvariant {

    private Expr condition;

    private boolean converted;

    public Invariant(Expr condition) {
        this(condition, false);
    }

    public Invariant(Expr condition, Boolean converted) {
        this.condition = condition;
        addPotentialFailure(this);
        this.converted = converted;
    }

    public boolean isConverted() {
        return converted;
    }

    public Expr getCondition() {
        return condition;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
