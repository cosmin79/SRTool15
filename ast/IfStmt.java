package ast;

public class IfStmt extends Stmt {

    private Expr condition;

    private BlockStmt thenBlock;

    private BlockStmt elseBlock;

    public IfStmt(Expr condition, BlockStmt thenBlock, BlockStmt elseBlock) {
        this.condition = condition;
        this.thenBlock = thenBlock;
        this.elseBlock = elseBlock;
    }

    public Expr getCondition() {
        return condition;
    }

    public BlockStmt getThenBlock() {
        return thenBlock;
    }

    public BlockStmt getElseBlock() {
        return elseBlock;
    }
}
