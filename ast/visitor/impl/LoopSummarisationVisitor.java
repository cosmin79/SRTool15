package ast.visitor.impl;

import ast.*;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;

public class LoopSummarisationVisitor extends DefaultVisitor {

    public LoopSummarisationVisitor(Map<Node, Node> pred) {
        super(pred);
    }

    @Override
    public Object visit(WhileStmt whileStmt) {
        Expr condition = (Expr) whileStmt.getCondition().accept(this);

        List<AssertStmt> invariantStmts = new LinkedList<>();
        // establish invariants hold on entry
        for (LoopInvariant invariant: whileStmt.getLoopInvariantList()) {
            if (invariant instanceof Invariant) {
                Invariant newInvariant = (Invariant) invariant.accept(this);
                AssertStmt assertInvariant = new AssertStmt(newInvariant.getCondition());
                predMap.put(assertInvariant, invariant);
                invariantStmts.add(assertInvariant);
            }
        }

        BlockStmt body = (BlockStmt) whileStmt.getBody().accept(this);

        List<Stmt> stmtList = new LinkedList<>();
        stmtList.addAll(invariantStmts);

        // teleport to arbitrary loop iteration satisfying the invariant
        for (String modVar: body.getModSet()) {
            stmtList.add(new HavocStmt(new VarRef(new VarIdentifier(modVar))));
        }
        for (AssertStmt invariantStmt: invariantStmts) {
            stmtList.add(new AssumeStmt(invariantStmt.getCondition()));
        }

        // if the loop condition still holds make sure the body behaves correctly
        List<Stmt> ifStmts = new LinkedList<>();
        ifStmts.add(body);
        ifStmts.addAll(invariantStmts);
        // block further loop execution
        ifStmts.add(new AssumeStmt(NumberExpr.FALSE));

        stmtList.add(new IfStmt(condition, new BlockStmt(ifStmts), new BlockStmt()));

        return new BlockStmt(stmtList);
    }
}
