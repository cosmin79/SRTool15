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

public class CRandom implements Callable<SMTReturnCode> {

    private static final int MAX_ITERATIONS = 2;

    private static final int COMPILE_TIMEOUT = 2;

    private static final int RUN_TIMEOUT = 3;

    private static final String MAIN = "main";

    private static final String INCLUDE_ASSERT_LIBRARY = "#include <cassert>\n" +
            "#include <ctime>\n" +
            "#include <cstdlib>\n";

    private static final String DIV_FUNC = "int mydiv(int a, int b) { return !b ? a : a / b;}\n";

    private static final String LEFT_SHIFT_FUNC = "int myleftshift(int a, int b) { return b >= 32 ? 0 : (a << b);}\n";

    private static final String METHOD = "foo%s";

    private Program program;

    private DebugUtil debugUtil;

    private final String testPath;

    public CRandom(Program program, DebugUtil debugUtil, String testPath) {
        this.program = program;
        this.debugUtil = debugUtil;
        this.testPath = testPath;
    }

    private boolean applyMethodSummarisation(Map<Node, Node> predMap) {
        program = (Program) new MethodSummarisationVisitor(predMap, program).visit(program);
        debugUtil.print("Code after method summarisation is applied:\n" + new PrintVisitor().visit(program));
        return Thread.currentThread().isInterrupted();
    }

    private boolean applyNonCFeaturesRemoval(Map<Node, Node> predMap) {
        program = (Program) new ToCVisitor(predMap, program).visit(program);
        debugUtil.print("All non C features removed:\n" + new PrintVisitor().visit(program));
        return Thread.currentThread().isInterrupted();
    }

    private boolean applyLoopSummarisation(Map<Node, Node> predMap) {
        program = (Program) new LoopSummarisationVisitor(predMap).visit(program);
        debugUtil.print("Code after loop summarisation is applied:\n" + new PrintVisitor().visit(program));
        return Thread.currentThread().isInterrupted();
    }

    private SMTReturnCode verifyMethod(String methodName, String program) {
        program = program.replaceFirst(methodName, MAIN);
        debugUtil.print("Program this iteration:\n" + program);

        String folderPrefix = SRTool.BIN_DIR + "/start_";
        String currSource = folderPrefix + testPath + ".cpp";

        // compile program
        try {
            PrintWriter writer = new PrintWriter(currSource);
            writer.println(program);
            writer.close();
        } catch (FileNotFoundException e) {
            return SMTReturnCode.UNKNOWN;
        }

        String execFile = folderPrefix + testPath;
        // run program
        try {
            ProcessExec process = new ProcessExec("g++", currSource, "-o", execFile);
            process.execute("", COMPILE_TIMEOUT);
        } catch (Exception e) {
            return SMTReturnCode.UNKNOWN;
        }

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
    public SMTReturnCode call() {
        Map<Node, Node> predMap = new HashMap<>();
        if (applyMethodSummarisation(predMap)) {
            return SMTReturnCode.UNKNOWN;
        }
        if (applyNonCFeaturesRemoval(predMap)) {
            return SMTReturnCode.UNKNOWN;
        }

        Program targetProgram = program;

        // applying loop summary in an attempt to find bad inputs
        if (applyLoopSummarisation(predMap)) {
            return SMTReturnCode.UNKNOWN;
        }

        MethodVerifier methodVerifier = new MethodVerifier(predMap, program, debugUtil);
        for(ProcedureDecl proc: program.getProcedureDecls()) {
            SMTResult smtResult;
            try {
                smtResult = methodVerifier.verifyMethod(proc);
            } catch (Exception e) {
                return SMTReturnCode.UNKNOWN;
            }

            if (smtResult.getReturnCode() == SMTReturnCode.INCORRECT) {
                String code = INCLUDE_ASSERT_LIBRARY + DIV_FUNC + LEFT_SHIFT_FUNC +
                        new PrintCVisitor(
                                proc.getMethodName(),
                                SmtUtil.getNodeValues(predMap, smtResult)).visit(targetProgram);
                SMTReturnCode returnCode = verifyMethod(proc.getMethodName(), code);
                if (returnCode == SMTReturnCode.INCORRECT) {
                    return returnCode;
                }
            }
        }

        return SMTReturnCode.CORRECT;
    }
}
