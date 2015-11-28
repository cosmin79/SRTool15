package tool.strategy;

import ast.Node;
import ast.ProcedureDecl;
import ast.Program;
import ast.visitor.impl.*;
import tool.*;
import util.ProcessExec;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.Callable;

public class CRandom implements Callable<SMTResult> {

    private static final int COMPILE_TIMEOUT = 2;

    private static final int RUN_TIMEOUT = 3;

    private static final String MAIN = "main";

    private static final String INCLUDE_ASSERT_LIBRARY = "#include <cassert>\n" +
            "#include <ctime>\n" +
            "#include <cstdlib>\n";

    private static final String LAST_32_BITS = "const long long LAST_32_BITS = (1LL << 32) - 1;\n";

    private static final String DIV_FUNC = "inline int mydiv(int a, int b) {" +
            "return !b ? a : a / b;}\n";

    private static final String MOD_FUNC = "inline int mymod(int a, int b) {" +
            "return !b ? a : a % b;}\n";

    private static final String ADD_FUNC = "inline int myadd(int a, int b) {" +
            "return (int)((1LL * a + b) & LAST_32_BITS);}\n";

    private static final String SUB_FUNC = "inline int mysub(int a, int b) {" +
            "return (int)((1LL * a - b) & LAST_32_BITS);}\n";

    private static final String MUL_FUNC = "inline int mymul(int a, int b) {" +
            "return (int)((1LL * a * b) & LAST_32_BITS);}\n";

    private static final String LEFT_SHIFT_FUNC = "inline int myleftshift(int a, int b) {" +
            "return b >= 32 ? 0 : (a << b);}\n";

    private static final String RIGHT_SHIFT_FUNC = "inline int myrightshift(int a, int b) {" +
            "b = b >= 32 ? 31 : b; return a >> b;}\n";

    private static final String METHOD = "foo%s";

    private Program program;

    private DebugUtil debugUtil;

    private final String testPath;

    private SMTResult smtResult;

    private Map<Node, Node> parentStrategyPredMap;

    private String strategyName;

    public CRandom(
            String strategyName,
            Program program,
            DebugUtil debugUtil,
            String testPath,
            SMTResult smtResult,
            Map<Node, Node> predMap) {
        this.program = program;
        this.debugUtil = debugUtil;
        this.testPath = testPath;
        this.smtResult = smtResult;
        this.strategyName = strategyName;
        parentStrategyPredMap = predMap;
    }

    private SMTReturnCode verifyMethod(String methodName, String program) {
        program = program.replaceFirst(methodName, MAIN);
        debugUtil.print("Program this iteration:\n" + program);

        String folderPrefix = SRTool.BIN_DIR + "/start_" + strategyName + "_";
        String currSource = folderPrefix + testPath + ".cpp";

        try {
            PrintWriter writer = new PrintWriter(currSource);
            writer.println(program);
            writer.close();
        } catch (FileNotFoundException e) {
            return SMTReturnCode.UNKNOWN;
        }

        // compile program
        String execFile = folderPrefix + testPath;
        try {
            ProcessExec process = new ProcessExec("g++", currSource, "-o", execFile);
            process.execute("", COMPILE_TIMEOUT);
            if (process.stderr != null && process.stderr.contains("error")) {
                return SMTReturnCode.UNKNOWN;
            }
        } catch (Exception e) {
            return SMTReturnCode.UNKNOWN;
        }

        // run program
        ProcessExec process = new ProcessExec("./" + execFile);
        try {
            process.execute("", RUN_TIMEOUT);
        } catch (Exception e) {
            return SMTReturnCode.UNKNOWN;
        }

        if (process.stderr != null && process.stderr.contains("failed")) {
            return SMTReturnCode.INCORRECT;
        }

        return Thread.currentThread().isInterrupted() ? SMTReturnCode.UNKNOWN :
                SMTReturnCode.MAYBE_COREECT;
    }

    // This strategy transforms the initial program into C++ and then attempts to find failing tests
    @Override
    public SMTResult call() {
        if (smtResult.getReturnCode() == SMTReturnCode.INCORRECT) {
            String failedMethodName = smtResult.getFailedMethod().getMethodName();
            String code = INCLUDE_ASSERT_LIBRARY +
                    LAST_32_BITS +
                    DIV_FUNC +
                    MOD_FUNC +
                    ADD_FUNC +
                    SUB_FUNC +
                    MUL_FUNC +
                    LEFT_SHIFT_FUNC +
                    RIGHT_SHIFT_FUNC +
                    new PrintCVisitor(program,
                            failedMethodName,
                            SmtUtil.getNodeValues(parentStrategyPredMap, smtResult)).visit(program);
            SMTReturnCode returnCode = verifyMethod(failedMethodName, code);
            if (returnCode == SMTReturnCode.INCORRECT) {
                return new SMTResult(returnCode);
            }
        }

        return new SMTResult(SMTReturnCode.UNKNOWN);
    }
}
