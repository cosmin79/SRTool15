package tool;

import ast.AssertStmt;
import ast.ProcedureDecl;
import ast.Program;
import util.ProcessExec;
import util.ProcessTimeoutException;

import java.io.IOException;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

enum SMTReturnCode {
    CORRECT, INCORRECT, UNKNOWN;
}

class SMTResult {

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

public class MethodVerifier {

    private static final int TIMEOUT = 30;

    private static final String BOOL_FAILED_REGEX = "%s false";

    private final Program program;

    private final DebugUtil debugUtil;

    public MethodVerifier(Program program, DebugUtil debugUtil) {
        this.program = program;
        this.debugUtil = debugUtil;
    }

    public SMTResult verifyMethod(ProcedureDecl procedureDecl) throws IOException, InterruptedException {
        VCGenerator vcgen = new VCGenerator(program, procedureDecl, debugUtil);
        VCResult vcResult = vcgen.generateVC();

        ProcessExec process = new ProcessExec("./z3", "-smt2", "-in");
        String queryResult = "";
        try {
            queryResult = process.execute(vcResult.getQuery(), TIMEOUT);
        } catch (ProcessTimeoutException e) {
            debugUtil.print("Call to z3 timed out\n");
            return new SMTResult(SMTReturnCode.UNKNOWN);
        }

        debugUtil.print(String.format("Result:\n%s\n", queryResult));
        if (queryResult.startsWith("sat")) {
            // obtain failed assertions
            List<AssertStmt> failedAssertions = parseFailedAssertions(queryResult, vcResult.getBooleanToAssert());
            return new SMTResult(SMTReturnCode.INCORRECT, failedAssertions);
        }

        if (!queryResult.startsWith("unsat")) {
            return new SMTResult(SMTReturnCode.UNKNOWN);
        }

        return new SMTResult(SMTReturnCode.CORRECT);
    }

    private List<AssertStmt> parseFailedAssertions(String queryResult, Map<String, AssertStmt> booleanToAssert) {
        List<AssertStmt> failedAsserts = new LinkedList<>();
        for (Map.Entry<String, AssertStmt> entryCond: booleanToAssert.entrySet()) {
            if (queryResult.contains(String.format(BOOL_FAILED_REGEX, entryCond.getKey()))) {
                failedAsserts.add(entryCond.getValue());
            }
        }

        return failedAsserts;
    }
}
