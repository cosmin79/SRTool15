package tool;

import ast.*;
import ast.visitor.impl.DefaultVisitor;

import java.util.LinkedList;
import java.util.List;

public class VCCVisitor extends DefaultVisitor {

    private static final String ASSIGN_STMT = "(assert (= %s %s))\n";

    private static final String NUMBER = "(_ bv%s 32)";

    private static final String TRUE_EXPR = "(_ bv1 32)";

    private List<String> facts;

    private List<String> assertConditions;

    public VCCVisitor() {
        assertConditions = new LinkedList<>();
        assertConditions.add(TRUE_EXPR);
        facts = new LinkedList<>();
    }

    public String getSmtResult() {
        StringBuilder sb = new StringBuilder();
        for (String fact: facts) {
            sb.append(fact);
        }
        sb.append("\n");

        if (!assertConditions.isEmpty()) {
            String andAssertions = assertConditions.get(0);
            for (int i = 1; i < assertConditions.size(); i++) {
                andAssertions = SmtUtil.applyBinary("&&", andAssertions, assertConditions.get(i));
            }
            andAssertions = String.format(SmtUtil.TO_BOOL_EXPR, andAssertions);

            sb.append(String.format("(assert (not %s))", andAssertions));
        }

        return sb.toString();
    }

    @Override
    public String visit(AssignStmt assignStmt) {
        String lhsVar = (String) assignStmt.getLhsVar().accept(this);
        String rhsExpr = (String) assignStmt.getRhsExpr().accept(this);
        facts.add(String.format(ASSIGN_STMT, lhsVar, rhsExpr));

        return "";
    }

    @Override
    public String visit(AssertStmt assertStmt) {
        assertConditions.add((String) assertStmt.getCondition().accept(this));

        return "";
    }

    @Override
    public String visit(BlockStmt blockStmt) {
        for (Stmt stmt: blockStmt.getStmts()) {
            stmt.accept(this);
        }

        return "";
    }

    @Override
    public String visit(TernExpr ternExpr) {
        String cond = (String) ternExpr.getCondition().accept(this);
        String thenVal = (String) ternExpr.getThenExpr().accept(this);
        String elseVal = (String) ternExpr.getElseExpr().accept(this);

        return SmtUtil.applyTern(cond, thenVal, elseVal);
    }

    @Override
    public String visit(BinaryExpr binaryExpr) {
        String lhs = (String) binaryExpr.getLhs().accept(this);
        String rhs = (String) binaryExpr.getRhs().accept(this);

        return SmtUtil.applyBinary(binaryExpr.getBinaryOp(), lhs, rhs);
    }

    @Override
    public String visit(UnaryExpr unaryExpr) {
        String arg = (String) unaryExpr.getArg().accept(this);

        return SmtUtil.applyUnary(unaryExpr.getUnaryOp(), arg);
    }

    @Override
    public String visit(NumberExpr numberExpr) {
        return String.format(NUMBER, numberExpr.getNumber().toString());
    }

    @Override
    public String visit(VarRefExpr varRefExpr) {
        return (String) varRefExpr.getVarRef().accept(this);
    }

    @Override
    public String visit(ParenExpr parenExpr) {
        return (String) parenExpr.getExpr().accept(this);
    }

    @Override
    public String visit(VarRef varRef) {
        return (String) varRef.getVarIdentifier().accept(this);
    }

    @Override
    public String visit(VarIdentifier varIdentifier) {
        return varIdentifier.getVarName();
    }
}
