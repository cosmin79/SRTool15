package ast.visitor.impl;

import ast.*;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

public class BMCVisitor extends DefaultVisitor {

    private BmcType soundType;

    private Integer maxDepth;

    private Map<WhileStmt, Integer> unwindDepth;

    private Map<AssertStmt, WhileStmt> stopAsserts;

    public BMCVisitor(Map<Node, Node> predMap, int maxDepth) {
        super(predMap);
        this.soundType = BmcType.UNSOUND;
        this.maxDepth = maxDepth;
    }

    public BMCVisitor(Map<Node, Node> predMap, Map<WhileStmt, Integer> unwindDepth, BmcType soundType) {
        super(predMap);
        this.soundType = soundType;
        this.unwindDepth = unwindDepth;
        this.stopAsserts = new HashMap<>();
    }

    public Map<AssertStmt, WhileStmt> getStopAsserts() {
        return stopAsserts;
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
                AssertStmt newAssertStmt = new AssertStmt(newInvariant.getCondition());
                predMap.put(newAssertStmt, invariant);

                invariantStmts.add(newAssertStmt);
            }
        }
        BlockStmt assertInvariantsBlock = new BlockStmt(invariantStmts);

        // last if statement
        List<Stmt> stmtListThen = new LinkedList<>();
        // invariants hold in the end
        stmtListThen.add(assertInvariantsBlock);
        if (soundType == BmcType.SOUND) {
            AssertStmt assertFalse = new AssertStmt(NumberExpr.FALSE);
            assertFalse.setIsBMCStop(true);
            stmtListThen.add(assertFalse);
            stopAsserts.put(assertFalse, whileStmt);
        }
        stmtListThen.add(new AssumeStmt(NumberExpr.FALSE));
        IfStmt resultIf = new IfStmt(condition, new BlockStmt(stmtListThen), new BlockStmt());

        int noIterations = soundType != BmcType.UNSOUND ? unwindDepth.get(whileStmt) : maxDepth;
        for (int iteration = 1; iteration <= noIterations; iteration++) {
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
