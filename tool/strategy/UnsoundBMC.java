package tool.strategy;

import ast.Node;
import ast.ProcedureDecl;
import ast.Program;
import ast.visitor.impl.*;
import tool.DebugUtil;
import tool.MethodVerifier;
import tool.SMTResult;
import tool.SMTReturnCode;

import java.io.IOException;
import java.util.concurrent.Callable;
import java.util.HashMap;
import java.util.Map;

public class UnsoundBMC implements Callable<SMTReturnCode> {

  private final static Integer MAX_UNWIND = 20;

  private Program program;

  private DebugUtil debugUtil;

  public UnsoundBMC(Program program, DebugUtil debugUtil) {
      this.program = program;
      this.debugUtil = debugUtil;
  }

  private boolean applyMethodSummarisation(Map<Node, Node> predMap) {
    program = (Program) new MethodSummarisationVisitor(predMap, program).visit(program);
    debugUtil.print("Code after method summarisation is applied:\n" +
                    new PrintVisitor().visit(program));
    return Thread.currentThread().isInterrupted();
  }

  // unsound BMC
  private boolean applyLoopUnwinding(Map<Node, Node> predMap) {
    program = (Program) new BMCVisitor(predMap, MAX_UNWIND).visit(program);
    debugUtil.print("Code after loop unwinding is applied:\n" +
                    new PrintVisitor().visit(program));
    program = (Program) new ShadowVisitor(predMap, program).visit(program);
    debugUtil.print("Code after shadow visiting is applied:\n" +
                    new PrintVisitor().visit(program));
    return Thread.currentThread().isInterrupted();
  }

  private SMTReturnCode checkMethod(MethodVerifier methodVerifier, ProcedureDecl proc) {
    SMTReturnCode retCode;
    try {
      retCode = methodVerifier.verifyMethod(proc).getReturnCode();
    } catch (Exception exception) {
      retCode = SMTReturnCode.UNKNOWN;
    }
    if (Thread.currentThread().isInterrupted()) {
      retCode = SMTReturnCode.UNKNOWN;
    }
    return retCode;
  }

  // This strategy uses unsound BMC for loops. It attempts to prove the program
  // is incorrect.
  // It may give false positives. No false negatives though!
  @Override
  public SMTReturnCode call() {
    Map<Node, Node> predMap = new HashMap<>();
    if (applyMethodSummarisation(predMap)) {
      return SMTReturnCode.UNKNOWN;
    }
    if (applyLoopUnwinding(predMap)) {
      return SMTReturnCode.UNKNOWN;
    }
    MethodVerifier methodVerifier = new MethodVerifier(predMap, program, debugUtil);
    for(ProcedureDecl proc: program.getProcedureDecls()) {
      SMTReturnCode retCode = checkMethod(methodVerifier, proc);
      if (retCode != SMTReturnCode.CORRECT) {
        return retCode;
      }
    }
    return SMTReturnCode.CORRECT;
  }
}
