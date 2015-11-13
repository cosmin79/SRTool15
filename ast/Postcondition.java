package ast;

public class Postcondition extends PrePostCondition {

    private Expr condition;

    public Postcondition(Expr condition) {
        this.condition = condition;
    }

    public Expr getCondition() {
        return condition;
    }
}
