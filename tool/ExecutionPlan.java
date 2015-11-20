package tool;

import ast.*;
import ast.visitor.impl.*;
import tool.strategy.Houdini;
import tool.strategy.LoopAndMethodSummary;
import tool.strategy.SoundBMC;
import tool.strategy.UnsoundBMC;

import java.io.IOException;
import java.util.*;

import java.util.concurrent.Executors;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;

public class ExecutionPlan {

  private DebugUtil debugUtil;
  private final Program program;
  private final int TIMEOUT = 120;

  public ExecutionPlan(Program program, DebugUtil debugUtil) {
      this.program = program;
      this.debugUtil = debugUtil;
  }

  private void decide(SMTReturnCode returnCode) {
    switch (returnCode) {
      case UNKNOWN:
        System.out.println("UNKNOWN");
        System.exit(1);
        break ;
      case INCORRECT:
        System.out.println("INCORRECT");
        System.exit(0);
        break ;
      case CORRECT:
        System.out.println("CORRECT");
        System.exit(0);
        break ;
    }
  }

  private Program cloneProgram() {
    return cloneProgram(new HashMap<>());
  }

  private Program cloneProgram(Map<Node, Node> pred) {
    return (Program) new DefaultVisitor(pred).visit(program);
  }

  private SMTReturnCode getReturnCode(Future<SMTReturnCode> future) {
    SMTReturnCode retCode;
    try {
      retCode = future.get(1, TimeUnit.SECONDS);
    } catch (Exception exception) {
      retCode = SMTReturnCode.UNKNOWN;
    }
    return retCode;
  }

  public void verifyProgram() {
    ExecutorService executor = Executors.newFixedThreadPool(4);
    Future<SMTReturnCode> loopAndMethodSummary =
      executor.submit(new LoopAndMethodSummary(cloneProgram(), debugUtil));
    Future<SMTReturnCode> houdini =
      executor.submit(new Houdini(cloneProgram(), debugUtil));
    Future<SMTReturnCode> unsoundBMC =
      executor.submit(new UnsoundBMC(cloneProgram(), debugUtil));
    Future<SMTReturnCode> soundBMC =
      executor.submit(new SoundBMC(cloneProgram(), debugUtil));
    try {
      executor.awaitTermination(TIMEOUT, TimeUnit.SECONDS);
    } catch (Exception exception) {
      decide(SMTReturnCode.UNKNOWN);
    }

    // Loop and method summary yields no false positives!
    SMTReturnCode returnCode = getReturnCode(loopAndMethodSummary);
    if (returnCode != SMTReturnCode.INCORRECT) {
      decide(returnCode);
    } else {
      // Houdini yields no false positives!
      returnCode = getReturnCode(houdini);
      if (returnCode != SMTReturnCode.INCORRECT) {
        decide(returnCode);
      } else {
        // This is kind of stupid; looking for a bug up to a particular depth. No false negatives though!
        returnCode = getReturnCode(unsoundBMC);
        if (returnCode != SMTReturnCode.CORRECT) {
          decide(returnCode);
        } else {
          // this applied sound BMC. We need a timeout version though as it might not terminate...
          // if it returns something it should be correct
          returnCode = getReturnCode(soundBMC);
          decide(returnCode);
        }
      }
    }
  }
}
