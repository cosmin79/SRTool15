package ast;

import ast.visitor.Visitor;

public class CandidateInvariant extends LoopInvariant {

    private Expr condition;

    public CandidateInvariant(Expr condition) {
        this.condition = condition;
        addPotentialFailures(this);
    }

    public Expr getCondition() {
        return condition;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
