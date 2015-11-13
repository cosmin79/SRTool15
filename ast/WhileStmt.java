package ast;

import java.util.List;

public class WhileStmt extends Stmt {

    private Expr condition;

    private List<LoopInvariant> loopInvariantList;

    private BlockStmt body;

    public WhileStmt(Expr condition, List<LoopInvariant> loopInvariantsList, BlockStmt body) {
        this.condition = condition;
        this.loopInvariantList = loopInvariantsList;
        this.body = body;
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
}
