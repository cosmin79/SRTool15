package ast;

public class Invariant extends LoopInvariant {

    private Expr condition;

    public Invariant(Expr condition) {
        this.condition = condition;
    }

    public Expr getCondition() {
        return condition;
    }
}
