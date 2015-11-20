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
import java.util.HashMap;
import java.util.Map;

import java.util.concurrent.Callable;

public class LoopAndMethodSummary implements Callable<SMTReturnCode> {

  private Program program;

  private DebugUtil debugUtil;

  public LoopAndMethodSummary(Program program, DebugUtil debugUtil) {
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

  private boolean applyLoopSummarisation(Map<Node, Node> predMap) {
    program = (Program) new LoopSummarisationVisitor(predMap).visit(program);
    debugUtil.print("Code after loop summarisation is applied:\n" + new PrintVisitor().visit(program));
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

  // This strategy uses loop and method summarisation.
  // It attempts to prove the program is correct
  // It may give false negatives. No false positives though!
  @Override
  public SMTReturnCode call() {
    Map<Node, Node> predMap = new HashMap<>();
    if (applyShadowVisitor(predMap)) {
      return SMTReturnCode.UNKNOWN;
    }
    if (applyMethodSummarisation(predMap)) {
      return SMTReturnCode.UNKNOWN;
    }
    if (applyLoopSummarisation(predMap)) {
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
