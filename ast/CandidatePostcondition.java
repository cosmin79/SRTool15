package ast;

public class CandidatePostcondition extends PrePostCondition {

    private Expr condition;

    public CandidatePostcondition(Expr condition) {
        this.condition = condition;
    }

    public Expr getCondition() {
        return condition;
    }
}
