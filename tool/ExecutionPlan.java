package tool;

import ast.*;
import ast.visitor.impl.*;
import tool.strategy.Houdini;
import tool.strategy.LoopAndMethodSummary;
import tool.strategy.SoundBMC;
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
        //SMTReturnCode returnCode = new Houdini(cloneProgram(), debugUtil).run();
        //decide(returnCode);

        // Loop and method summary yields no false positives!
        SMTReturnCode returnCode = new LoopAndMethodSummary(cloneProgram(), debugUtil).run();
        if (returnCode != SMTReturnCode.INCORRECT) {
            decide(returnCode);
        } else {
            // Houdini yields no false positives!
            returnCode = new Houdini(cloneProgram(), debugUtil).run();
            if (returnCode != SMTReturnCode.INCORRECT) {
                decide(returnCode);
            } else {
                // This is kind of stupid ; looking for a bug up to a particular depth. No false negatives though!
                returnCode = new UnsoundBMC(cloneProgram(), debugUtil).run();
                if (returnCode != SMTReturnCode.CORRECT) {
                    decide(returnCode);
                } else {
                    // this applied sound BMC. We need a timeout version though as it might not terminate...
                    // if it returns something it should be correct
                    returnCode = new SoundBMC(cloneProgram(), debugUtil).run();
                    decide(returnCode);
                }
            }
        }
    }
}
