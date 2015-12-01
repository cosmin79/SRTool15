package ast;

import ast.visitor.Visitor;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

public class UnaryExpr extends Expr {

    private static final Set<String> usefulHoudiniOperators = new HashSet<String>() {{
        add("-"); add("~");
    }};

    private String unaryOp;

    private Expr arg;

    public UnaryExpr(String unaryOp, Expr arg) {
        this.unaryOp = unaryOp;
        this.arg = arg;
    }

    public String getUnaryOp() {
        return unaryOp;
    }

    public Expr getArg() {
        return arg;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }

    @Override
    public Set<String> getRefVars() {
        return arg.getRefVars();
    }

    @Override
    public Boolean isCandidateHoudini() {
        return usefulHoudiniOperators.contains(unaryOp);
    }

    @Override
    public List<Expr> getExprs() {
        List<Expr> underlyingExprs = new LinkedList<>();
        underlyingExprs.add(this);
        underlyingExprs.addAll(arg.getExprs());

        return underlyingExprs;
    }
}
