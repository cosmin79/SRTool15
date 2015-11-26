package tool;

import ast.*;
import ast.visitor.impl.DefaultVisitor;

import java.util.*;

public class SSAVisitor extends DefaultVisitor {

    private ScopesHandler scopesHandler;

    private Map<String, Node> varToDeclNode;

    public Map<String, Node> getVarToDeclNode() {
        return varToDeclNode;
    }

    public SSAVisitor(Map<Node, Node> predMap, Program program, VariableIdsGenerator variableIdsGenerator) {
        super(predMap);
        scopesHandler = new ScopesHandler(variableIdsGenerator);
        varToDeclNode = new HashMap<>();
        for (VarDecl varDecl: program.getVarDecls()) {
            String varName = varDecl.getVarIdentifier().getVarName();
            scopesHandler.addGlobalVariable(varName);
            varToDeclNode.put(scopesHandler.latestVar(varName), varDecl);
        }
    }

    @Override
    public Object visit(VarDecl varDecl) {
        String varName = varDecl.getVarIdentifier().getVarName();
        scopesHandler.addVariable(varName);
        varToDeclNode.put(scopesHandler.latestVar(varName), varDecl);

        BlockStmt blockStmt = new BlockStmt();
        blockStmt.addModSet(varName);

        return blockStmt;
    }

    @Override
    public Object visit(ProcedureDecl procedureDecl) {
        scopesHandler.pushStack();
        scopesHandler.pushMethodsStack(procedureDecl);
        List<Stmt> stmts = new LinkedList<>();

        // add parameters to stack
        for (FormalParam param: procedureDecl.getParamList()) {
            String varName = param.getVarIdentifier().getVarName();
            scopesHandler.addVariable(varName);
            varToDeclNode.put(scopesHandler.latestVar(varName), param);
        }

        // handle preconditions
        for (PrePostCondition prePostCondition: procedureDecl.getPrePostConditions()) {
            if (prePostCondition instanceof Precondition) {
                scopesHandler.addAssumption((Expr) prePostCondition.accept(this));
            }
        }

        // method body
        for (Stmt stmt: procedureDecl.getStmts()) {
            stmts.add((Stmt) stmt.accept(this));
        }

        // handle postconditions
        for (PrePostCondition prePostCondition: procedureDecl.getPrePostConditions()) {
            if (prePostCondition instanceof Postcondition) {
                Expr newCond = scopesHandler.generateCondition((Expr) prePostCondition.accept(this));
                AssertStmt assertPostCond = new AssertStmt(newCond);
                predMap.put(assertPostCond, prePostCondition);
                stmts.add(assertPostCond);
            }
        }

        scopesHandler.popStack();
        scopesHandler.popMethodsStack();

        return new BlockStmt(stmts);
    }

    @Override
    public Object visit(Precondition precondition) {
        return precondition.getCondition().accept(this);
    }

    @Override
    public Object visit(Postcondition postcondition) {
        return postcondition.getCondition().accept(this);
    }

    @Override
    public Object visit(CandidatePrecondition candidatePrecondition) {
        return candidatePrecondition.getCondition().accept(this);
    }

    @Override
    public Object visit(CandidatePostcondition candidatePostcondition) {
        return candidatePostcondition.getCondition().accept(this);
    }

    @Override
    public Object visit(AssignStmt assignStmt) {
        String varName = assignStmt.getLhsVar().getVarIdentifier().getVarName();

        Expr rhsExpr = (Expr) assignStmt.getRhsExpr().accept(this);
        scopesHandler.addVariable(varName);
        VarRef lhsVar = (VarRef) assignStmt.getLhsVar().accept(this);

        AssignStmt result = new AssignStmt(lhsVar, rhsExpr);
        result.addModSet(varName);

        return result;
    }

    @Override
    public Object visit(AssertStmt assertStmt) {
        Expr condExpr = (Expr) assertStmt.getCondition().accept(this);
        AssertStmt newAssertStmt = new AssertStmt(scopesHandler.generateCondition(condExpr));
        predMap.put(newAssertStmt, assertStmt);

        return newAssertStmt;
    }

    @Override
    public Object visit(AssumeStmt assumeStmt) {
        Expr condExpr = (Expr) assumeStmt.getCondition().accept(this);
        scopesHandler.addAssumption(condExpr);

        // generate an empty block
        return new BlockStmt();
    }

    @Override
    public Object visit(HavocStmt havocStmt) {
        String varName = havocStmt.getVar().getVarIdentifier().getVarName();
        scopesHandler.addVariable(varName);
        varToDeclNode.put(scopesHandler.latestVar(varName), havocStmt);

        BlockStmt result = new BlockStmt();
        result.addModSet(varName);

        return result;
    }

    private Expr varRefExpr(String varName) {
        return new VarRefExpr(new VarRef(new VarIdentifier(varName)));
    }

    private Expr generateNewIfValue(Expr cond, String varThen, String varElse) {
        if (varThen == null) {
            return varRefExpr(varElse);
        } else if (varElse == null) {
            return varRefExpr(varThen);
        }

        return new TernExpr(cond, varRefExpr(varThen), varRefExpr(varElse));
    }

    @Override
    public Object visit(IfStmt ifStmt) {
        Expr condExpr = (Expr) ifStmt.getCondition().accept(this);

        // then branch
        ScopeInfo thenScope = scopesHandler.pushStack();
        scopesHandler.addCondition(condExpr);
        BlockStmt thenBlock = (BlockStmt) ifStmt.getThenBlock().accept(this);
        scopesHandler.popStack();

        // else branch
        ScopeInfo elseScope = scopesHandler.pushStack();
        scopesHandler.addCondition(new UnaryExpr("!", condExpr));
        BlockStmt elseBlock = (BlockStmt) ifStmt.getElseBlock().accept(this);
        scopesHandler.popStack();

        List<Stmt> stmtList = new LinkedList<>();
        stmtList.add(thenBlock);
        stmtList.add(elseBlock);

        // update modified variables
        Set<String> modSet = thenBlock.getModSet();
        modSet.addAll(elseBlock.getModSet());
        for (String modifiedVar: modSet) {
            String thenValue = scopesHandler.varFromGivenScopeOrGlobal(thenScope, modifiedVar);
            String elseValue = scopesHandler.varFromGivenScopeOrGlobal(elseScope, modifiedVar);
            // new value of variable
            Expr newExpr = generateNewIfValue(condExpr, thenValue, elseValue);

            // generate new label for variable
            scopesHandler.addVariable(modifiedVar);
            stmtList.add(new AssignStmt(
                    new VarRef(new VarIdentifier(scopesHandler.latestVar(modifiedVar))),
                    newExpr));
        }

        return new BlockStmt(stmtList);
    }

    @Override
    public Object visit(ResultExpr resultExpr) {
        return scopesHandler.getEnclosingMethod().getReturnExpr().accept(this);
    }

    @Override
    public Object visit(OldExpr oldExpr) {
        String oldVarName = scopesHandler.getOldGlobal(oldExpr.getVar().getVarIdentifier().getVarName());

        return varRefExpr(oldVarName);
    }

    @Override
    public Object visit(VarIdentifier varIdentifier) {
        return new VarIdentifier(scopesHandler.latestVar(varIdentifier.getVarName()));
    }
}
