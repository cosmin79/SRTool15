package ast;

import ast.visitor.Visitor;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

public class BinaryExpr extends Expr {

    private static final Set<String> usefulHoudiniOperators = new HashSet<String>() {{
        add("|"); add("&"); add("^");
        add("<<"); add(">>");
        add("+"); add("-"); add("*"); add("/"); add("%");
    }};

    private String binaryOp;

    private Expr lhs;

    private Expr rhs;

    public BinaryExpr(String binaryOp, Expr lhs, Expr rhs) {
        this.binaryOp = binaryOp;
        this.lhs = lhs;
        this.rhs = rhs;
    }

    public String getBinaryOp() {
        return binaryOp;
    }

    public Expr getLhs() {
        return lhs;
    }

    public Expr getRhs() {
        return rhs;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }

    @Override
    public Set<String> getRefVars() {
        Set<String> result = new HashSet<>();
        result.addAll(lhs.getRefVars());
        result.addAll(rhs.getRefVars());

        return result;
    }

    @Override
    public Boolean isCandidateHoudini() {
        return usefulHoudiniOperators.contains(binaryOp);
    }

    @Override
    public List<Expr> getExprs() {
        List<Expr> underlyingExprs = new LinkedList<>();
        underlyingExprs.add(this);
        underlyingExprs.addAll(lhs.getExprs());
        underlyingExprs.addAll(rhs.getExprs());

        return underlyingExprs;
    }
}
