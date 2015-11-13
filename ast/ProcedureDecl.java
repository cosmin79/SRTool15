package ast;

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
        this.stmts = stmts;
        this.returnExpr = returnExpr;
    }

    public String getMethodName() {
        return methodName;
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
}
