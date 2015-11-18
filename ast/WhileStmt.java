package ast;

import ast.visitor.Visitor;

import java.util.List;

public class WhileStmt extends Stmt {

    private Expr condition;

    private List<LoopInvariant> loopInvariantList;

    private BlockStmt body;

    public WhileStmt(Expr condition, List<LoopInvariant> loopInvariantsList, BlockStmt body) {
        this.condition = condition;
        this.loopInvariantList = loopInvariantsList;
        for (LoopInvariant loopInvariant: loopInvariantsList) {
            addPotentialFailures(loopInvariant);
        }
        this.body = body;
        addModSet(body);
        addPotentialFailures(body);
        addLoop(this);
        addLoops(body);
    }

    public Expr getCondition() {
        return condition;
    }

    public List<LoopInvariant> getLoopInvariantList() {
        return loopInvariantList;
    }

    public BlockStmt getBody() {
        return body;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
