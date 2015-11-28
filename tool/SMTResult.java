package tool;

import ast.AssertStmt;
import ast.Node;
import ast.ProcedureDecl;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

public class SMTResult {

    private SMTReturnCode returnCode;

    private List<AssertStmt> failedAsserts;

    private Map<Node, Integer> varNodeToValue;

    private ProcedureDecl failedMethod;

    public SMTResult(
            List<AssertStmt> failedAsserts,
            Map<Node, Integer> varNodeToValue,
            ProcedureDecl failedMethod) {
        this.returnCode = SMTReturnCode.INCORRECT;
        this.failedAsserts = failedAsserts;
        this.varNodeToValue = varNodeToValue;
        this.failedMethod = failedMethod;
    }

    public SMTResult(SMTReturnCode returnCode) {
        this.returnCode = returnCode;
    }

    public SMTReturnCode getReturnCode() {
        return returnCode;
    }

    public List<AssertStmt> getFailedAsserts() {
        return failedAsserts;
    }

    public Map<Node, Integer> getVarNodeToValue() {
        return varNodeToValue;
    }

    public ProcedureDecl getFailedMethod() {
        return failedMethod;
    }
}
