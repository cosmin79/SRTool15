package ast.visitor.impl;

import ast.*;
import ast.visitor.Visitor;

import java.util.LinkedList;
import java.util.List;

public class DefaultVisitor implements Visitor<Object> {

    @Override
    public Object visit(Program program) {
        List<VarDecl> globals = new LinkedList<>();
        List<ProcedureDecl> procedures = new LinkedList<>();

        for (VarDecl varDecl: program.getVarDecls()) {
            globals.add((VarDecl) varDecl.accept(this));
        }

        for (ProcedureDecl procedureDecl: program.getProcedureDecls()) {
            procedures.add((ProcedureDecl) procedureDecl.accept(this));
        }

        return new Program(globals, procedures);
    }

    @Override
    public Object visit(VarDecl varDecl) {
        return new VarDecl((VarIdentifier) varDecl.getVarIdentifier().accept(this));
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
        return new Precondition((Expr) precondition.getCondition().accept(this));
    }

    @Override
    public Object visit(Postcondition postcondition) {
        return new Postcondition((Expr) postcondition.getCondition().accept(this));
    }

    @Override
    public Object visit(CandidatePrecondition candidatePrecondition) {
        return new CandidatePrecondition((Expr) candidatePrecondition.getCondition().accept(this));
    }

    @Override
    public Object visit(CandidatePostcondition candidatePostcondition) {
        return new CandidatePostcondition((Expr) candidatePostcondition.getCondition().accept(this));
    }

    @Override
    public Object visit(AssignStmt assignStmt) {
        Expr rhsExpr = (Expr) assignStmt.getRhsExpr().accept(this);
        VarRef lhsVar = (VarRef) assignStmt.getLhsVar().accept(this);

        return new AssignStmt(lhsVar, rhsExpr);
    }

    @Override
    public Object visit(AssertStmt assertStmt) {
        return new AssertStmt((Expr) assertStmt.getCondition().accept(this));
    }

    @Override
    public Object visit(AssumeStmt assumeStmt) {
        return new AssumeStmt((Expr) assumeStmt.getCondition().accept(this));
    }

    @Override
    public Object visit(HavocStmt havocStmt) {
        return new HavocStmt((VarRef) havocStmt.getVar().accept(this));
    }

    @Override
    public Object visit(CallStmt callStmt) {
        String methodName = callStmt.getMethodName();

        List<Expr> parameters = new LinkedList<>();
        for (Expr expr: callStmt.getParametersList()) {
            parameters.add((Expr) expr.accept(this));
        }

        VarRef lhsVar = (VarRef) callStmt.getLhsVar().accept(this);

        return new CallStmt(lhsVar, methodName, parameters);
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
        return new Invariant((Expr) invariant.getCondition().accept(this));
    }

    @Override
    public Object visit(CandidateInvariant candidateInvariant) {
        return new CandidateInvariant((Expr) candidateInvariant.getCondition().accept(this));
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
