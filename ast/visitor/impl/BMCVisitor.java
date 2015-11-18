package ast.visitor.impl;

import ast.*;

import java.util.LinkedList;
import java.util.List;

public class BMCVisitor extends DefaultVisitor {

    private Boolean sound;

    private Integer maxDepth;

    // For now assume only unsound BMC
    public BMCVisitor(Boolean sound, int maxDepth) {
        this.sound = sound;
        this.maxDepth = maxDepth;
    }

    // Assume unsound for now
    @Override
    public Object visit(WhileStmt whileStmt) {
        Expr condition = (Expr) whileStmt.getCondition().accept(this);
        BlockStmt body = (BlockStmt) whileStmt.getBody().accept(this);

        // Obtain a block of the invariants
        List<Stmt> invariantStmts = new LinkedList<>();
        for (LoopInvariant invariant: whileStmt.getLoopInvariantList()) {
            if (invariant instanceof Invariant) {
                Invariant newInvariant = (Invariant) invariant.accept(this);
                invariantStmts.add(new AssertStmt(newInvariant.getCondition()));
            }
        }
        BlockStmt assertInvariantsBlock = new BlockStmt(invariantStmts);

        // last if statement
        List<Stmt> stmtListThen = new LinkedList<>();
        // invariants hold in the end
        stmtListThen.add(assertInvariantsBlock);
        stmtListThen.add(new AssumeStmt(NumberExpr.FALSE));
        IfStmt resultIf = new IfStmt(condition, new BlockStmt(stmtListThen), new BlockStmt());

        for (int iteration = 1; iteration <= maxDepth; iteration++) {
            List<Stmt> newIfBlock = new LinkedList<>();
            newIfBlock.add(body);
            // invariants hold in every iteration
            newIfBlock.add(assertInvariantsBlock);
            newIfBlock.add(resultIf);
            resultIf = new IfStmt(condition, new BlockStmt(newIfBlock), new BlockStmt());
        }

        List<Stmt> resultBlockStms = new LinkedList<>();
        // invariants hold in the beggining
        resultBlockStms.add(assertInvariantsBlock);
        resultBlockStms.add(resultIf);

        return new BlockStmt(resultBlockStms);
    }
}
