package tool.strategy;

import ast.Node;
import ast.ProcedureDecl;
import ast.Program;
import ast.visitor.impl.LoopSummarisationVisitor;
import ast.visitor.impl.MethodSummarisationVisitor;
import ast.visitor.impl.PrintVisitor;
import org.omg.CORBA.UNKNOWN;
import tool.DebugUtil;
import tool.MethodVerifier;
import tool.SMTResult;
import tool.SMTReturnCode;

import java.util.Map;
import java.util.concurrent.Callable;

public class LoopAndMethodSummary implements Callable<SMTResult> {

  private Program program;

  private DebugUtil debugUtil;

  private Map<Node, Node> predMap;

  private String testPath;

  public LoopAndMethodSummary(Program program, DebugUtil debugUtil, String testPath, Map<Node, Node> predMap) {
    this.program = program;
    this.debugUtil = debugUtil;
    this.predMap = predMap;
    this.testPath = testPath;
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

  private SMTResult checkMethod(MethodVerifier methodVerifier, ProcedureDecl proc) {
    SMTResult smtResult;
    try {
      smtResult = methodVerifier.verifyMethod(proc);
    } catch (Exception exception) {
      smtResult = new SMTResult(SMTReturnCode.UNKNOWN);
    }
    if (Thread.currentThread().isInterrupted()) {
      smtResult = new SMTResult(SMTReturnCode.UNKNOWN);
    }
    return smtResult;
  }

  // This strategy uses loop and method summarisation.
  // It attempts to prove the program is correct
  // It may give false negatives. No false positives though!
  @Override
  public SMTResult call() {
    if (applyMethodSummarisation(predMap)) {
      return new SMTResult(SMTReturnCode.UNKNOWN);
    }
    Program programWithoutCalls = program;

    if (applyLoopSummarisation(predMap)) {
      return new SMTResult(SMTReturnCode.UNKNOWN);
    }
    MethodVerifier methodVerifier = new MethodVerifier(predMap, program, debugUtil);
    for (ProcedureDecl proc : program.getProcedureDecls()) {
      debugUtil.print("Analyzing method: " + proc.getMethodName());
      SMTResult smtResult = checkMethod(methodVerifier, proc);

      switch (smtResult.getReturnCode()) {
        case UNKNOWN:
          return smtResult;
        case INCORRECT:
          SMTResult cResult = new CRandom(programWithoutCalls, debugUtil, testPath, smtResult, predMap).call();
          if (cResult.getReturnCode() == SMTReturnCode.INCORRECT) {
            return cResult;
          } else {
            return new SMTResult(SMTReturnCode.UNKNOWN);
          }
      }
    }
    return new SMTResult(SMTReturnCode.CORRECT);
  }
}
