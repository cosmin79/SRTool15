package tool;

import ast.AssertStmt;

import java.util.LinkedList;
import java.util.List;

public class SMTResult {

    private SMTReturnCode returnCode;

    private List<AssertStmt> failedAsserts;

    public SMTResult(SMTReturnCode returnCode, List<AssertStmt> failedAsserts) {
        this.returnCode = returnCode;
        this.failedAsserts = failedAsserts;
    }

    public SMTResult(SMTReturnCode returnCode) {
        this(returnCode, new LinkedList<>());
    }

    public SMTReturnCode getReturnCode() {
        return returnCode;
    }

    public List<AssertStmt> getFailedAsserts() {
        return failedAsserts;
    }
}
