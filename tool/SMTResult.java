package tool;

import ast.AssertStmt;
import ast.Node;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

public class SMTResult {

    private SMTReturnCode returnCode;

    private List<AssertStmt> failedAsserts;

    private Map<Node, Integer> varNodeToValue;

    public SMTResult(SMTReturnCode returnCode, List<AssertStmt> failedAsserts, Map<Node, Integer> varNodeToValue) {
        this.returnCode = returnCode;
        this.failedAsserts = failedAsserts;
        this.varNodeToValue = varNodeToValue;
    }

    public SMTResult(SMTReturnCode returnCode) {
        this(returnCode, new LinkedList<>(), new HashMap<>());
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
}
