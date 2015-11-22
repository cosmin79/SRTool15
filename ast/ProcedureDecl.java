package ast;

import ast.visitor.Visitor;

import java.util.LinkedList;
import java.util.List;

public class ProcedureDecl extends Node {

    private String methodName;

    private List<FormalParam> paramList = new LinkedList<>();

    private List<PrePostCondition> prePostConditions = new LinkedList<>();

    private List<Stmt> stmts = new LinkedList<>();

    private Expr returnExpr;

    public ProcedureDecl(String methodName,
                         List<FormalParam> paramList,
                         List<PrePostCondition> prePostConditions,
                         List<Stmt> stmts,
                         Expr returnExpr) {
        this.methodName = methodName;
        this.paramList = paramList;
        this.prePostConditions = prePostConditions;
        for (PrePostCondition prePostCondition: prePostConditions) {
            addPotentialFailures(prePostCondition);
        }
        this.stmts = stmts;
        this.returnExpr = returnExpr;
        for (Stmt stmt: stmts) {
            addModSet(stmt);
            addPotentialFailures(stmt);
            addLoops(stmt);
        }
    }

    public String getMethodName() {
        return methodName;
    }

    public void setMethodName(String methodName) {
        this.methodName = methodName;
    }

    public List<FormalParam> getParamList() {
        return paramList;
    }

    public List<PrePostCondition> getPrePostConditions() {
        return prePostConditions;
    }

    public List<Stmt> getStmts() {
        return stmts;
    }

    public Expr getReturnExpr() {
        return returnExpr;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
