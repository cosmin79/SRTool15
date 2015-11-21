package tool.strategy;

import ast.Node;
import ast.ProcedureDecl;
import ast.Program;
import ast.visitor.impl.*;
import tool.DebugUtil;
import tool.SMTReturnCode;
import util.ProcessExec;

import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.Callable;

public class CRandom implements Callable<SMTReturnCode> {

    private static final int MAX_ITERATIONS = 10;

    private static final int COMPILE_TIMEOUT = 2;

    private static final int RUN_TIMEOUT = 8;

    private static final String MAIN = "main";

    private static final String INCLUDE_ASSERT_LIBRARY = "#include <cassert>\n";

    private Program program;

    private DebugUtil debugUtil;

    public CRandom(Program program, DebugUtil debugUtil) {
        this.program = program;
        this.debugUtil = debugUtil;
    }

    private boolean applyShadowVisitor(Map<Node, Node> predMap) {
        program = (Program) new ShadowVisitor(predMap, program).visit(program);
        program = (Program) new DefaultVisitor(predMap).visit(program);
        debugUtil.print("Code after shadow visiting is applied:\n" + new PrintVisitor().visit(program));
        return Thread.currentThread().isInterrupted();
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

    private SMTReturnCode verifyMethod(String methodName, String program) {
        program = program.replaceFirst(methodName, MAIN);
        debugUtil.print("Program this iteration:\n" + program) ;
        // compile program
        try {
            PrintWriter writer = new PrintWriter("test.cpp");
            writer.println(program);
            writer.close();
        } catch (FileNotFoundException e) {
            return SMTReturnCode.UNKNOWN;
        }

        // run program
        try {
            ProcessExec process = new ProcessExec("g++", "test.cpp", "-o", "test");
            process.execute("", COMPILE_TIMEOUT);
        } catch (Exception e) {
            return SMTReturnCode.UNKNOWN;
        }

        ProcessExec process = new ProcessExec("./test");
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
        if (applyShadowVisitor(predMap)) {
            return SMTReturnCode.UNKNOWN;
        }
        if (applyMethodSummarisation(predMap)) {
            return SMTReturnCode.UNKNOWN;
        }
        if (applyNonCFeaturesRemoval(predMap)) {
            return SMTReturnCode.UNKNOWN;
        }
        String code = INCLUDE_ASSERT_LIBRARY + new PrintCVisitor(program).visit(program);
        debugUtil.print("Final C program:\n" + code + "\n");

        for (int noIterations = 0; noIterations < MAX_ITERATIONS; noIterations++) {
            for (ProcedureDecl procedureDecl: program.getProcedureDecls()) {
                SMTReturnCode returnCode = verifyMethod(procedureDecl.getMethodName(), code);
                if (returnCode == SMTReturnCode.INCORRECT || returnCode == SMTReturnCode.UNKNOWN) {
                    return returnCode;
                }
            }
        }

        return SMTReturnCode.MAYBE_COREECT;
    }
}
