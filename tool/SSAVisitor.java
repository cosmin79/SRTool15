package tool;

import ast.*;
import ast.visitor.impl.DefaultVisitor;

import java.util.LinkedList;
import java.util.List;
import java.util.Set;

public class SSAVisitor extends DefaultVisitor {

    private ScopesHandlerNew scopesHandler;

    public SSAVisitor(Program program) {
        scopesHandler = new ScopesHandlerNew(new VariableIdsGenerator());
        for (VarDecl varDecl: program.getVarDecls()) {
            scopesHandler.addGlobalVariable(varDecl.getVarIdentifier().getVarName());
        }
    }

    @Override
    public Object visit(VarDecl varDecl) {
        String varName = varDecl.getVarIdentifier().getVarName();
        scopesHandler.addVariable(varName);

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
            scopesHandler.addVariable(param.getVarIdentifier().getVarName());
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
                stmts.add(new AssertStmt(newCond));
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

        return new AssertStmt(scopesHandler.generateCondition(condExpr));
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

        BlockStmt result = new BlockStmt();
        result.addModSet(varName);

        return result;
    }

    private Expr varRefExpr(String varName) {
        return new VarRefExpr(new VarRef(new VarIdentifier(varName)));
    }

    @Override
    public Object visit(IfStmt ifStmt) {
        Expr condExpr = (Expr) ifStmt.getCondition().accept(this);

        // then branch
        // TODO(ccarabet): maybe create a new stack here and keep that as a reference
        scopesHandler.pushStack();
        scopesHandler.addCondition(condExpr);
        BlockStmt thenBlock = (BlockStmt) ifStmt.getThenBlock().accept(this);
        ScopeInfoNew thenScope = scopesHandler.popStack();

        // else branch
        scopesHandler.pushStack();
        scopesHandler.addCondition(new UnaryExpr("!", condExpr));
        BlockStmt elseBlock = (BlockStmt) ifStmt.getElseBlock().accept(this);
        ScopeInfoNew elseScope = scopesHandler.popStack();

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
            Expr newExpr = new TernExpr(condExpr, varRefExpr(thenValue), varRefExpr(elseValue));

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
