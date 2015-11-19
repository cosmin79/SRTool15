package ast;

import ast.visitor.Visitor;

public class AssertStmt extends Stmt {

    private Expr condition;

    private Boolean isBMCStop;

    public AssertStmt(Expr condition) {
        this.condition = condition;
        isBMCStop = false;
        addPotentialFailure(this);
    }

    public Expr getCondition() {
        return condition;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }

    public Boolean getIsBMCStop() {
        return isBMCStop;
    }

    public void setIsBMCStop(Boolean isBMCStop) {
        this.isBMCStop = isBMCStop;
    }
}
