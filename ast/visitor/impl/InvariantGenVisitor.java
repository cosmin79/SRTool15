package ast.visitor.impl;

import ast.*;
import tool.ScopesHandler;
import tool.VariableIdsGenerator;

import java.util.*;

public class InvariantGenVisitor extends DefaultVisitor {

    private static final String GLOBAL_COPY = "%s_copy";

    private static final String AUX_ITER = "iter";

    // those are operators that we're going to use
    private final List<String> operators = Arrays.asList("<", "<=", "==", "!=", ">=", ">");

    private static final Expr ONE = new NumberExpr(Long.valueOf(1));

    private static final Expr MINUS_ONE = new UnaryExpr("-", new NumberExpr(Long.valueOf(1)));

    boolean isInsideLoopCond;

    private final List<Expr> interestingConstants = Arrays.asList(
            MINUS_ONE, new NumberExpr(Long.valueOf(0)), ONE);

    private List<Expr> interestingAssertsCurrMethod;

    private Map<String, List<Expr>> interestingVarChanges;

    private ScopesHandler scopesHandler;

    public InvariantGenVisitor(Map<Node, Node> predMap, Program program) {
        super(predMap);
        scopesHandler = new ScopesHandler(new VariableIdsGenerator());
        for (VarDecl varDecl: program.getVarDecls()) {
            scopesHandler.addGlobalVariable(varDecl.getVarIdentifier().getVarName());
        }
        isInsideLoopCond = false;
    }

    private VarRef generateVarRef(String varName) {
        return new VarRef(new VarIdentifier(varName));
    }

    private VarRefExpr generateVarExpr(String varName) {
        return new VarRefExpr(generateVarRef(varName));
    }

    @Override
    public Object visit(WhileStmt whileStmt) {
        List<Stmt> newStmts = new LinkedList<>();
        List<LoopInvariant> loopInvariants = new LinkedList<>();

        isInsideLoopCond = true;
        Expr condition = (Expr) whileStmt.getCondition().accept(this);
        isInsideLoopCond = false;
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

        // add copies after modified variables
        for (String modVar: modifiedVariables) {
            String globalCopy = String.format(GLOBAL_COPY, modVar);
            newStmts.add(new VarDecl(new VarIdentifier(globalCopy)));
            newStmts.add(new AssignStmt(generateVarRef(globalCopy), generateVarExpr(modVar)));
        }
        // add an auxiliary iterator variable
        newStmts.add(new VarDecl(new VarIdentifier(AUX_ITER)));
        newStmts.add(new AssignStmt(generateVarRef(AUX_ITER), new NumberExpr(0L)));

        // create new while body
        List<Stmt> whileBodyStmts = new LinkedList<>();
        whileBodyStmts.add(body);
        whileBodyStmts.add(new AssignStmt(
                generateVarRef(AUX_ITER),
                new BinaryExpr("+", generateVarExpr(AUX_ITER), new NumberExpr(1L))));

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

        // add a candidate invariant: compare modified var with interesting constants
        for (String operator: operators) {
            for (String lhsVar: modifiedVariables) {
                for (Expr rhsExpr: scopesHandler.getUsedExprs()) {
                    if (isExprWellDefined(rhsExpr, usedVariables)) {
                        loopInvariants.add(new CandidateInvariant(
                                new BinaryExpr(operator, generateVarExpr(lhsVar), rhsExpr)));
                    }
                }
            }
        }

        // add candidate invariants for all interesting boolean conditions (assumes and asserts)
        for (Expr assumeExpr: interestingAssertsCurrMethod) {
            if (isExprWellDefined(assumeExpr, usedVariables)) {
                loopInvariants.add(new CandidateInvariant(assumeExpr));
            }
        }

        // add candidate invariants for all interesting modifed var changes
        // i.e. x = copy_x + iter * change_expr e.g. x = copy_x + iter * (-2)
        for (String modVar: modifiedVariables) {
            if (interestingVarChanges.containsKey(modVar)) {
                for (Expr loopChange: interestingVarChanges.get(modVar)) {
                    if (isExprWellDefined(loopChange, usedVariables)) {
                        loopInvariants.add(new CandidateInvariant(
                                new BinaryExpr("==",
                                        generateVarExpr(modVar),
                                        new BinaryExpr("+",
                                                generateVarExpr(String.format(GLOBAL_COPY, modVar)),
                                                        new BinaryExpr("*",
                                                                generateVarExpr(AUX_ITER),
                                                                loopChange)))));
                    }
                }
            }
        }

        // create the while statement with the right body
        newStmts.add(new WhileStmt(condition, loopInvariants, new BlockStmt(whileBodyStmts)));

        return new BlockStmt(newStmts);
    }

    private boolean isExprWellDefined(Expr expr, Set<String> existingVars) {
        for (String refVar: expr.getRefVars()) {
            if (!existingVars.contains(refVar)) {
                return false;
            }
        }
        return true;
    }

    @Override
    public Object visit(AssignStmt assignStmt) {
        String varName = assignStmt.getLhsVar().getVarIdentifier().getVarName();
        Expr rhsExpr = (Expr) assignStmt.getRhsExpr().accept(this);
        VarRef lhsVar = (VarRef) assignStmt.getLhsVar().accept(this);
        AssignStmt newAssignStmt = new AssignStmt(lhsVar, rhsExpr);
        newAssignStmt.addModSet(varName);

        List<Expr> interestingExprsCurrVar = interestingVarChanges.get(varName);
        if (interestingExprsCurrVar == null) {
            interestingExprsCurrVar = new LinkedList<>();
        }
        // add candidate var changes
        for (Expr underlyingExpr: rhsExpr.getExprs()) {
            if (!underlyingExpr.getRefVars().contains(varName) && underlyingExpr.isCandidateHoudini()) {
                interestingExprsCurrVar.add(underlyingExpr);
                interestingExprsCurrVar.add(new UnaryExpr("-", underlyingExpr));
            }
        }
        interestingVarChanges.put(varName, interestingExprsCurrVar);

        return newAssignStmt;
    }

    @Override
    public Object visit(ProcedureDecl procedureDecl) {
        scopesHandler.pushStack();
        // record existing assumes
        interestingAssertsCurrMethod = new LinkedList<>();
        for (AssumeStmt assumeStmt: procedureDecl.getAssumeStmts()) {
            interestingAssertsCurrMethod.add(assumeStmt.getCondition());
        }
        // record existing asserts
        for (Node criticalNode: procedureDecl.getPotentiallyCriticalFailures()) {
            if (criticalNode instanceof AssertStmt) {
                interestingAssertsCurrMethod.add(((AssertStmt) criticalNode).getCondition());
            }
        }
        // reset tracking of var changes
        interestingVarChanges = new HashMap<>();

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
        if (isInsideLoopCond) {
            if (expr.isCandidateHoudini()) {
                // especially useful for bounds checking...
                scopesHandler.addExpr(new BinaryExpr("+", expr, ONE));
                scopesHandler.addExpr(new BinaryExpr("-", expr, ONE));
            }
        } else {
            if (expr.getRefVars().isEmpty()) {
                scopesHandler.addExpr(expr);
            }
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
