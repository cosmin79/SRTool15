package ast.visitor.impl;

import ast.*;

import java.util.LinkedList;
import java.util.List;

public class LoopSummarisationVisitor extends DefaultVisitor {

    @Override
    public Object visit(WhileStmt whileStmt) {
        Expr condition = (Expr) whileStmt.getCondition().accept(this);
        List<Expr> loopInvariants = new LinkedList<>();

        for (LoopInvariant invariant: whileStmt.getLoopInvariantList()) {
            if (invariant instanceof Invariant) {
                Invariant newInvariant = (Invariant) invariant.accept(this);
                loopInvariants.add(newInvariant.getCondition());
            }
        }

        BlockStmt body = (BlockStmt) whileStmt.getBody().accept(this);

        List<Stmt> stmtList = new LinkedList<>();
        // establish invariants hold on entry
        for (Expr invariant: loopInvariants) {
            stmtList.add(new AssertStmt(invariant));
        }

        // teleport to arbitrary loop iteration satisfying the invariant
        for (String modVar: body.getModSet()) {
            stmtList.add(new HavocStmt(new VarRef(new VarIdentifier(modVar))));
        }
        for (Expr invariant: loopInvariants) {
            stmtList.add(new AssumeStmt(invariant));
        }

        // if the loop condition still holds make sure the body behaves correctly
        List<Stmt> ifStmts = new LinkedList<>();
        ifStmts.add(body);
        for (Expr invariant: loopInvariants) {
            ifStmts.add(new AssertStmt(invariant));
        }
        // block further loop execution
        ifStmts.add(new AssumeStmt(NumberExpr.FALSE));

        stmtList.add(new IfStmt(condition, new BlockStmt(ifStmts), new BlockStmt()));

        return new BlockStmt(stmtList);
    }
}
