package ast;

public class Precondition extends PrePostCondition {

    private Expr condition;

    public Precondition(Expr condition) {
        this.condition = condition;
    }

    public Expr getCondition() {
        return condition;
    }
}
