package ast;

import ast.visitor.Visitor;

import java.util.LinkedList;
import java.util.List;

public class CallStmt extends Stmt {

    private VarRef lhsVar;

    private String methodName;

    private List<Expr> parametersList = new LinkedList<>();

    public CallStmt(VarRef lhsVar, String methodName, List<Expr> parametersList) {
        this.lhsVar = lhsVar;
        this.methodName = methodName;
        this.parametersList = parametersList;
        addModSet(lhsVar);
        addCall(this);
    }

    public VarRef getLhsVar() {
        return lhsVar;
    }

    public String getMethodName() {
        return methodName;
    }

    public List<Expr> getParametersList() {
        return parametersList;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
