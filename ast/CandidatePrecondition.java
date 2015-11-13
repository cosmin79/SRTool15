package ast;

public class CandidatePrecondition extends PrePostCondition {

    private Expr condition;

    public CandidatePrecondition(Expr condition) {
        this.condition = condition;
    }

    public Expr getCondition() {
        return condition;
    }
}
