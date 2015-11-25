package ast.visitor.impl;

import ast.*;
import ast.visitor.Visitor;

import java.util.*;

public class DefaultVisitor implements Visitor<Object> {

    protected Map<Node, Node> predMap;

    private Map<String, ProcedureDecl> methodNameToProcedure;

    public DefaultVisitor(Map<Node, Node> predMap) {
        this.predMap = predMap;
        methodNameToProcedure = new HashMap<>();
    }

    private Set<String> setDifference(Node given, Node target) {
        Set<String> setDifference = new HashSet<>();
        Set<String> givenModSet = given.getModSet();
        Set<String> targetModSet = target.getModSet();
        for (String modVar: givenModSet) {
            if (!targetModSet.contains(modVar)) {
                setDifference.add(modVar);
            }
        }

        return setDifference;
    }

    @Override
    public Object visit(Program program) {
        List<VarDecl> globals = new LinkedList<>();
        List<ProcedureDecl> procedures = new LinkedList<>();

        for (VarDecl varDecl: program.getVarDecls()) {
            globals.add((VarDecl) varDecl.accept(this));
        }

        for (ProcedureDecl procedureDecl: program.getProcedureDecls()) {
            procedures.add((ProcedureDecl) procedureDecl.accept(this));
            methodNameToProcedure.put(procedureDecl.getMethodName(), procedureDecl);
        }

        // solve modSet for calls
        boolean change = true;
        while (change) {
            change = false;
            for (ProcedureDecl procedureDecl: procedures) {
                for (CallStmt callStmt: procedureDecl.getCallStmts()) {
                    ProcedureDecl dependent = methodNameToProcedure.get(callStmt.getMethodName());
                    Set<String> setDifference = setDifference(dependent, procedureDecl);
                    if (!setDifference.isEmpty()) {
                        procedureDecl.addModSet(setDifference);
                        change = true;
                    }
                }
            }
        }

        return new Program(globals, procedures);
    }

    @Override
    public Object visit(VarDecl varDecl) {
        String varName = varDecl.getVarIdentifier().getVarName();
        VarDecl newVarDecl = new VarDecl((VarIdentifier) varDecl.getVarIdentifier().accept(this));
        newVarDecl.addModSet(varName);

        return newVarDecl;
    }

    @Override
    public Object visit(ProcedureDecl procedureDecl) {
        String methodName = procedureDecl.getMethodName();
        List<FormalParam> formalParams = new LinkedList<>();
        List<PrePostCondition> prePostConditions = new LinkedList<>();
        List<Stmt> stmts = new LinkedList<>();

        for (FormalParam param: procedureDecl.getParamList()) {
            formalParams.add((FormalParam) param.accept(this));
        }

        for (PrePostCondition prePostCondition: procedureDecl.getPrePostConditions()) {
            prePostConditions.add((PrePostCondition) prePostCondition.accept(this));
        }

        for (Stmt stmt: procedureDecl.getStmts()) {
            stmts.add((Stmt) stmt.accept(this));
        }

        Expr resultExpr = (Expr) procedureDecl.getReturnExpr().accept(this);

        return new ProcedureDecl(methodName, formalParams, prePostConditions, stmts, resultExpr);
    }

    @Override
    public Object visit(FormalParam formalParam) {
        return new FormalParam((VarIdentifier) formalParam.getVarIdentifier().accept(this));
    }

    @Override
    public Object visit(Precondition precondition) {
        Precondition newPrecondition = new Precondition((Expr) precondition.getCondition().accept(this));
        predMap.put(newPrecondition, precondition);

        return newPrecondition;
    }

    @Override
    public Object visit(Postcondition postcondition) {
        Postcondition newPostcondition = new Postcondition((Expr) postcondition.getCondition().accept(this));
        predMap.put(newPostcondition, postcondition);

        return newPostcondition;
    }

    @Override
    public Object visit(CandidatePrecondition candidatePrecondition) {
        CandidatePrecondition newCandidatePrecondition
                = new CandidatePrecondition((Expr) candidatePrecondition.getCondition().accept(this));
        predMap.put(newCandidatePrecondition, candidatePrecondition);

        return newCandidatePrecondition;
    }

    @Override
    public Object visit(CandidatePostcondition candidatePostcondition) {
        CandidatePostcondition newCandidatePostCondition
                = new CandidatePostcondition((Expr) candidatePostcondition.getCondition().accept(this));
        predMap.put(newCandidatePostCondition, candidatePostcondition);

        return newCandidatePostCondition;
    }

    @Override
    public Object visit(AssignStmt assignStmt) {
        String varName = assignStmt.getLhsVar().getVarIdentifier().getVarName();
        Expr rhsExpr = (Expr) assignStmt.getRhsExpr().accept(this);
        VarRef lhsVar = (VarRef) assignStmt.getLhsVar().accept(this);
        AssignStmt newAssignStmt = new AssignStmt(lhsVar, rhsExpr);
        newAssignStmt.addModSet(varName);

        return newAssignStmt;
    }

    @Override
    public Object visit(AssertStmt assertStmt) {
        AssertStmt newAssertStmt = new AssertStmt((Expr) assertStmt.getCondition().accept(this));
        predMap.put(newAssertStmt, assertStmt);

        return newAssertStmt;
    }

    @Override
    public Object visit(AssumeStmt assumeStmt) {
        return new AssumeStmt((Expr) assumeStmt.getCondition().accept(this));
    }

    @Override
    public Object visit(HavocStmt havocStmt) {
        String varName = havocStmt.getVar().getVarIdentifier().getVarName();
        HavocStmt newHavocStmt = new HavocStmt((VarRef) havocStmt.getVar().accept(this));
        newHavocStmt.addModSet(varName);

        return newHavocStmt;
    }

    @Override
    public Object visit(CallStmt callStmt) {
        String methodName = callStmt.getMethodName();
        String varName = callStmt.getLhsVar().getVarIdentifier().getVarName();

        List<Expr> parameters = new LinkedList<>();
        for (Expr expr: callStmt.getParametersList()) {
            parameters.add((Expr) expr.accept(this));
        }

        VarRef lhsVar = (VarRef) callStmt.getLhsVar().accept(this);
        CallStmt newCallStmt = new CallStmt(lhsVar, methodName, parameters);
        newCallStmt.addModSet(varName);

        return newCallStmt;
    }

    @Override
    public Object visit(IfStmt ifStmt) {
        Expr condition = (Expr) ifStmt.getCondition().accept(this);
        BlockStmt thenBlock = (BlockStmt) ifStmt.getThenBlock().accept(this);
        BlockStmt elseBlock = (BlockStmt) ifStmt.getElseBlock().accept(this);

        return new IfStmt(condition, thenBlock, elseBlock);
    }

    @Override
    public Object visit(WhileStmt whileStmt) {
        Expr condition = (Expr) whileStmt.getCondition().accept(this);
        List<LoopInvariant> loopInvariants = new LinkedList<>();
        BlockStmt body = (BlockStmt) whileStmt.getBody().accept(this);

        for (LoopInvariant invariant: whileStmt.getLoopInvariantList()) {
            loopInvariants.add((LoopInvariant) invariant.accept(this));
        }

        return new WhileStmt(condition, loopInvariants, body);
    }

    @Override
    public Object visit(BlockStmt blockStmt) {
        List<Stmt> stmts = new LinkedList<>();
        for (Stmt stmt: blockStmt.getStmts()) {
            stmts.add((Stmt) stmt.accept(this));
        }

        return new BlockStmt(stmts);
    }

    @Override
    public Object visit(Invariant invariant) {
        Invariant newInvariant = new Invariant((Expr) invariant.getCondition().accept(this));
        predMap.put(newInvariant, invariant);

        return newInvariant;
    }

    @Override
    public Object visit(CandidateInvariant candidateInvariant) {
        CandidateInvariant newCandidateInvariant
                = new CandidateInvariant((Expr) candidateInvariant.getCondition().accept(this));
        predMap.put(newCandidateInvariant, candidateInvariant);

        return newCandidateInvariant;
    }

    @Override
    public Object visit(TernExpr ternExpr) {
        Expr condition = (Expr) ternExpr.getCondition().accept(this);
        Expr thenExpr = (Expr) ternExpr.getThenExpr().accept(this);
        Expr elseExpr = (Expr) ternExpr.getElseExpr().accept(this);

        return new TernExpr(condition, thenExpr, elseExpr);
    }

    @Override
    public Object visit(BinaryExpr binaryExpr) {
        String binaryOp = binaryExpr.getBinaryOp();
        Expr lhs = (Expr) binaryExpr.getLhs().accept(this);
        Expr rhs = (Expr) binaryExpr.getRhs().accept(this);

        return new BinaryExpr(binaryOp, lhs, rhs);
    }

    @Override
    public Object visit(UnaryExpr unaryExpr) {
        String unaryOp = unaryExpr.getUnaryOp();
        Expr arg = (Expr) unaryExpr.getArg().accept(this);

        return new UnaryExpr(unaryOp, arg);
    }

    @Override
    public Object visit(NumberExpr numberExpr) {
        return new NumberExpr(numberExpr.getNumber());
    }

    @Override
    public Object visit(VarRefExpr varRefExpr) {
        return new VarRefExpr((VarRef) varRefExpr.getVarRef().accept(this));
    }

    @Override
    public Object visit(ParenExpr parenExpr) {
        return new ParenExpr((Expr) parenExpr.getExpr().accept(this));
    }

    @Override
    public Object visit(ResultExpr resultExpr) {
        return resultExpr;
    }

    @Override
    public Object visit(OldExpr oldExpr) {
        return new OldExpr((VarRef) oldExpr.getVar().accept(this));
    }

    @Override
    public Object visit(VarRef varRef) {
        return new VarRef((VarIdentifier) varRef.getVarIdentifier().accept(this));
    }

    @Override
    public Object visit(VarIdentifier varIdentifier) {
        return varIdentifier;
    }
}
