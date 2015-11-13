package ast;

public class CandidateInvariant extends LoopInvariant {

    private Expr condition;

    public CandidateInvariant(Expr condition) {
        this.condition = condition;
    }

    public Expr getCondition() {
        return condition;
    }
}
