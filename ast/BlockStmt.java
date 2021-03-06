package ast;

import ast.visitor.Visitor;

import java.util.LinkedList;
import java.util.List;

public class BlockStmt extends Stmt {

    private List<Stmt> stmts;

    public BlockStmt(List<Stmt> stmts) {
        this.stmts = stmts;
        for (Stmt stmt: stmts) {
            addModSet(stmt);
            addPotentialFailures(stmt);
            addLoops(stmt);
            addCalls(stmt);
        }
    }

    // Empty block
    public BlockStmt() {
        stmts = new LinkedList<>();
    }

    public List<Stmt> getStmts() {
        return stmts;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
