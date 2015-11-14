package ast;

import ast.visitor.Visitor;

public class CandidatePrecondition extends PrePostCondition {

    private Expr condition;

    public CandidatePrecondition(Expr condition) {
        this.condition = condition;
    }

    public Expr getCondition() {
        return condition;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
