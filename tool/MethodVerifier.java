package tool;

import ast.AssertStmt;
import ast.Node;
import ast.ProcedureDecl;
import ast.Program;
import util.ProcessExec;
import util.ProcessTimeoutException;

import java.io.IOException;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class MethodVerifier {

    private static final int TIMEOUT = 30;

    private static final String BOOL_FAILED_REGEX = "%s false";

    private static final String VAR_REGEX = "%s \\(_ bv([0-9]+) 32\\)";

    private final Program program;

    private final DebugUtil debugUtil;

    private Map<Node, Node> predMap;

    public MethodVerifier(Map<Node, Node> predMap, Program program, DebugUtil debugUtil) {
        this.predMap = predMap;
        this.program = program;
        this.debugUtil = debugUtil;
    }

    public SMTResult verifyMethod(ProcedureDecl procedureDecl) throws IOException, InterruptedException {
        VCGenerator vcgen = new VCGenerator(program, procedureDecl, debugUtil, predMap);
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
            return new SMTResult(
                    failedAssertions,
                    parseVariablesValue(queryResult, vcResult.getVarToNode()),
                    procedureDecl);
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

    private Integer parseUnsignedString(String no) {
        Long longUnsgined = Long.parseLong(no);
        Long firstBit = Long.valueOf(1 << 31);
        if ((longUnsgined & firstBit) > 0) {
            return Math.toIntExact(-(firstBit - (longUnsgined ^ firstBit)));
        }

        return Math.toIntExact(longUnsgined);
    }

    // Kind of inefficient I suppose
    private Map<Node, Integer> parseVariablesValue(String queryResult, Map<String, Node> varToNode) {
        Map<Node, Integer> variableValue = new HashMap<>();
        for (Map.Entry<String, Node> entryVarNode: varToNode.entrySet()) {
            String regexPattern = String.format(VAR_REGEX, entryVarNode.getKey());
            Pattern p = Pattern.compile(regexPattern);
            Matcher m = p.matcher(queryResult);
            m.find();
            variableValue.put(entryVarNode.getValue(), parseUnsignedString(m.group(1)));
        }

        return variableValue;
    }
}
