package ast.visitor.impl;

import ast.*;
import tool.ScopesHandler;
import tool.VariableIdsGenerator;

import java.util.*;

public class InvariantGenVisitor extends DefaultVisitor {

    // those are operators that we're going to use
    private final List<String> operators = Arrays.asList("<", "<=", "==", "!=", ">=", ">");

    private static final Expr ONE = new NumberExpr(1);

    private static final Expr MINUS_ONE = new UnaryExpr("-", new NumberExpr(1));

    boolean isInsideLoopCond;

    private final List<Expr> interestingConstants = Arrays.asList(
            MINUS_ONE, new NumberExpr(0), ONE);

    private ScopesHandler scopesHandler;

    public InvariantGenVisitor(Map<Node, Node> predMap, Program program) {
        super(predMap);
        scopesHandler = new ScopesHandler(new VariableIdsGenerator());
        for (VarDecl varDecl: program.getVarDecls()) {
            scopesHandler.addGlobalVariable(varDecl.getVarIdentifier().getVarName());
        }
        isInsideLoopCond = false;
    }

    private VarRefExpr generateVarExpr(String varName) {
        return new VarRefExpr(new VarRef(new VarIdentifier(varName)));
    }

    @Override
    public Object visit(WhileStmt whileStmt) {
        isInsideLoopCond = true;
        Expr condition = (Expr) whileStmt.getCondition().accept(this);
        isInsideLoopCond = false;
        List<LoopInvariant> loopInvariants = new LinkedList<>();
        BlockStmt body = (BlockStmt) whileStmt.getBody().accept(this);

        for (LoopInvariant invariant: whileStmt.getLoopInvariantList()) {
            loopInvariants.add((LoopInvariant) invariant.accept(this));
        }

        // attempting to generate new candidate invariants
        Set<String> usedVariables = scopesHandler.getDefinedVars();
        // we compute the modified variables that will be visible to the outside (after the loop)
        Set<String> modifiedVariables = new HashSet<>();
        for (String modifiedVar: body.getModSet()) {
            if (usedVariables.contains(modifiedVar)) {
                modifiedVariables.add(modifiedVar);
            }
        }

        // add a candidate invariant for this var and any other defined var
        for (String operator: operators) {
            for (String lhsVar : modifiedVariables) {
                for (String usedVar : usedVariables) {
                    if (!lhsVar.equals(usedVar)) {
                        loopInvariants.add(new CandidateInvariant(
                                new BinaryExpr(operator, generateVarExpr(lhsVar), generateVarExpr(usedVar))));
                    }
                }
            }
        }

        // add a candidate number invariant for every modified variable
        for (String operator: operators) {
            for (String lhsVar: modifiedVariables) {
                for (Expr rhsExpr: usefulExprsSoFar()) {
                    loopInvariants.add(new CandidateInvariant(
                            new BinaryExpr(operator, generateVarExpr(lhsVar), rhsExpr)));
                }
            }
        }


        return new WhileStmt(condition, loopInvariants, body);
    }

    private boolean isExprWellDefined(Expr expr, Set<String> existingVars) {
        for (String refVar: expr.getRefVars()) {
            if (!existingVars.contains(refVar)) {
                return false;
            }
        }
        return true;
    }

    private List<Expr> usefulExprsSoFar() {
        Set<String> usedVariables = scopesHandler.getDefinedVars();

        Set<Expr> candidateExprs = scopesHandler.getUsedExprs();
        // filter out expressions that reference non defined variables
        List<Expr> result = new LinkedList<>();
        for (Expr candidateExpr: candidateExprs) {
            if (candidateExpr.getRefVars().isEmpty()) {
                result.add(candidateExpr);
            }
        }
        candidateExprs.addAll(interestingConstants);

        return result;
    }

    @Override
    public Object visit(ProcedureDecl procedureDecl) {
        scopesHandler.pushStack();
        Object result = super.visit(procedureDecl);
        scopesHandler.popStack();

        return result;
    }

    @Override
    public Object visit(BlockStmt blockStmt) {
        scopesHandler.pushStack();
        Object result = super.visit(blockStmt);
        scopesHandler.popStack();

        return result;
    }

    @Override
    public Object visit(VarDecl varDecl) {
        scopesHandler.addVariable(varDecl.getVarIdentifier().getVarName());

        return super.visit(varDecl);
    }

    @Override
    public Object visit(FormalParam formalParam) {
        scopesHandler.addVariable(formalParam.getVarIdentifier().getVarName());

        return super.visit(formalParam);
    }

    private void addExpr(Expr expr) {
        scopesHandler.addExpr(expr);
        if (isInsideLoopCond) {
            // especially useful for bounds checking...
            scopesHandler.addExpr(new BinaryExpr("+", expr, ONE));
            scopesHandler.addExpr(new BinaryExpr("-", expr, ONE));
        }
    }

    @Override
    public Object visit(TernExpr ternExpr) {
        addExpr(ternExpr);
        return super.visit(ternExpr);
    }

    @Override
    public Object visit(BinaryExpr binaryExpr) {
        addExpr(binaryExpr);
        return super.visit(binaryExpr);
    }

    @Override
    public Object visit(UnaryExpr unaryExpr) {
        addExpr(unaryExpr);
        return super.visit(unaryExpr);
    }

    @Override
    public Object visit(NumberExpr numberExpr) {
        addExpr(numberExpr);
        return super.visit(numberExpr);
    }

    @Override
    public Object visit(VarRefExpr varRefExpr) {
        addExpr(varRefExpr);
        return super.visit(varRefExpr);
    }

    @Override
    public Object visit(OldExpr oldExpr) {
        addExpr(oldExpr);
        return super.visit(oldExpr);
    }
}
