package tool;

import ast.*;
import ast.visitor.impl.*;
import tool.strategy.LoopAndMethodSummary;
import tool.strategy.UnsoundBMC;

import java.io.IOException;
import java.util.*;

public class ExecutionPlan {

    private DebugUtil debugUtil;

    private final Program program;

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

    public void verifyProgram() throws IOException, InterruptedException {
        // apply strategy 1. It yields no false positives!
        SMTReturnCode returnCode = new LoopAndMethodSummary(cloneProgram(), debugUtil).run();
        if (returnCode != SMTReturnCode.INCORRECT) {
            decide(returnCode);
        } else {
            // note that strategy 2 is looking for bugs. It yields no false negatives;
            returnCode = new UnsoundBMC(cloneProgram(), debugUtil).run();
            if (returnCode != SMTReturnCode.CORRECT) {
                decide(returnCode);
            } else {
                // this applied sound BMC. We need a timeout version though as it might not terminate...
                returnCode = new UnsoundBMC(cloneProgram(), debugUtil).run();
                decide(returnCode);
                // By the way, in this strategy we might loop forever :D
            }
        }
    }
}
