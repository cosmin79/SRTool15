package ast;

import java.util.List;

public class BlockStmt extends Stmt {

    private List<Stmt> stmts;

    public BlockStmt(List<Stmt> stmts) {
        this.stmts = stmts;
    }

    public List<Stmt> getStmts() {
        return stmts;
    }
}
