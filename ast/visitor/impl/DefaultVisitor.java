package ast.visitor.impl;

import ast.*;
import ast.visitor.Visitor;
import tool.ScopesHandler;
import tool.VariableIdsGenerator;

import java.util.LinkedList;
import java.util.List;

public class DefaultVisitor implements Visitor<Node> {

    private ScopesHandler scopesHandler;

    public DefaultVisitor(VariableIdsGenerator freshIds, Program program) {
        scopesHandler = new ScopesHandler(freshIds);
        for (VarDecl varDecl: program.getVarDecls()) {
            scopesHandler.addGlobalVariable(varDecl.getVarIdentifier().getVarName());
        }
    }

    @Override
    public Node visit(Program program) {
        List<VarDecl> globals = new LinkedList<>();
        List<ProcedureDecl> procedures = new LinkedList<>();

        for (String globalVar: scopesHandler.getGlobalVariables()) {
            globals.add(new VarDecl(new VarIdentifier(scopesHandler.latestVar(globalVar))));
        }
        
        for (ProcedureDecl procedureDecl: program.getProcedureDecls()) {
            procedures.add((ProcedureDecl) visit(procedureDecl));
        }

        return new Program(globals, procedures);
    }

    @Override
    public Node visit(VarDecl varDecl) {
        return new VarDecl((VarIdentifier) visit(varDecl.getVarIdentifier()));
    }

    @Override
    public Node visit(ProcedureDecl procedureDecl) {
        String methodName = procedureDecl.getMethodName();
        List<FormalParam> formalParams = new LinkedList<>();
        List<PrePostCondition> prePostConditions = new LinkedList<>();
        List<Stmt> stmts = new LinkedList<>();

        for (FormalParam param: procedureDecl.getParamList()) {
            formalParams.add((FormalParam) visit(param));
        }

        for (PrePostCondition prePostCondition: procedureDecl.getPrePostConditions()) {
            prePostConditions.add((PrePostCondition) visit(prePostCondition));
        }

        for (Stmt stmt: procedureDecl.getStmts()) {
            stmts.add((Stmt) visit(stmt));
        }

        Expr resultExpr = (Expr) visit(procedureDecl.getReturnExpr());

        return new ProcedureDecl(methodName, formalParams, prePostConditions, stmts, resultExpr);
    }

    @Override
    public Node visit(FormalParam formalParam) {
        return new FormalParam((VarIdentifier) visit(formalParam.getVarIdentifier()));
    }

    @Override
    public Node visit(PrePostCondition prePostCondition) {
        if (prePostCondition instanceof Precondition) {
            return visit((Precondition) prePostCondition);
        } else if (prePostCondition instanceof Postcondition) {
            return visit((Postcondition) prePostCondition);
        } else if (prePostCondition instanceof CandidatePrecondition) {
            return visit((CandidatePrecondition) prePostCondition);
        }

        return visit((CandidatePostcondition) prePostCondition);
    }

    @Override
    public Node visit(Precondition precondition) {
        return new Precondition((Expr) visit(precondition.getCondition()));
    }

    @Override
    public Node visit(Postcondition postcondition) {
        return new Postcondition((Expr) visit(postcondition.getCondition()));
    }

    @Override
    public Node visit(CandidatePrecondition candidatePrecondition) {
        return new CandidatePrecondition((Expr) visit(candidatePrecondition.getCondition()));
    }

    @Override
    public Node visit(CandidatePostcondition candidatePostcondition) {
        return new CandidatePostcondition((Expr) visit(candidatePostcondition.getCondition()));
    }

    @Override
    public Node visit(Stmt stmt) {
        if (stmt instanceof VarDecl) {
            return visit((VarDecl) stmt);
        } else if (stmt instanceof AssignStmt) {
            return visit((AssignStmt) stmt);
        } else if (stmt instanceof AssertStmt) {
            return visit((AssertStmt) stmt);
        } else if (stmt instanceof AssumeStmt) {
            return visit((AssumeStmt) stmt);
        } else if (stmt instanceof HavocStmt) {
            return visit((HavocStmt) stmt);
        } else if (stmt instanceof CallStmt) {
            return visit((CallStmt) stmt);
        } else if (stmt instanceof IfStmt) {
            return visit((IfStmt) stmt);
        } else if (stmt instanceof WhileStmt) {
            return visit((WhileStmt) stmt);
        }

        return visit((BlockStmt) stmt);
    }

    @Override
    public Node visit(AssignStmt assignStmt) {
        return new AssignStmt((VarRef) visit(assignStmt.getLhsVar()), (Expr) visit(assignStmt.getRhsExpr()));
    }

    @Override
    public Node visit(AssertStmt assertStmt) {
        return new AssertStmt((Expr) visit(assertStmt.getCondition()));
    }

    @Override
    public Node visit(AssumeStmt assumeStmt) {
        return new AssumeStmt((Expr) visit(assumeStmt.getCondition()));
    }

    @Override
    public Node visit(HavocStmt havocStmt) {
        return new HavocStmt((VarRef) visit(havocStmt.getVar()));
    }

    @Override
    public Node visit(CallStmt callStmt) {
        VarRef lhsVar = (VarRef) visit(callStmt.getLhsVar());
        String methodName = callStmt.getMethodName();

        List<Expr> parameters = new LinkedList<>();
        for (Expr expr: callStmt.getParametersList()) {
            parameters.add((Expr) visit(expr));
        }

        return new CallStmt(lhsVar, methodName, parameters);
    }

    @Override
    public Node visit(IfStmt ifStmt) {
        Expr condition = (Expr) visit(ifStmt.getCondition());
        BlockStmt thenBlock = (BlockStmt) visit(ifStmt.getThenBlock());
        BlockStmt elseBlock = (BlockStmt) visit(ifStmt.getElseBlock());

        return new IfStmt(condition, thenBlock, elseBlock);
    }

    @Override
    public Node visit(WhileStmt whileStmt) {
        Expr condition = (Expr) visit(whileStmt.getCondition());
        List<LoopInvariant> loopInvariants = new LinkedList<>();
        BlockStmt body = (BlockStmt) visit(whileStmt.getBody());

        for (LoopInvariant invariant: whileStmt.getLoopInvariantList()) {
            loopInvariants.add((LoopInvariant) visit(invariant));
        }

        return new WhileStmt(condition, loopInvariants, body);
    }

    @Override
    public Node visit(BlockStmt blockStmt) {
        List<Stmt> stmts = new LinkedList<>();
        for (Stmt stmt: blockStmt.getStmts()) {
            stmts.add((Stmt) visit(stmt));
        }

        return new BlockStmt(stmts);
    }

    @Override
    public Node visit(LoopInvariant loopInvariant) {
        if (loopInvariant instanceof Invariant) {
            return visit((Invariant) loopInvariant);
        }

        return visit((CandidateInvariant) loopInvariant);
    }

    @Override
    public Node visit(Invariant invariant) {
        return new Invariant((Expr) visit(invariant.getCondition()));
    }

    @Override
    public Node visit(CandidateInvariant candidateInvariant) {
        return new CandidateInvariant((Expr) visit(candidateInvariant.getCondition()));
    }

    @Override
    public Node visit(Expr expr) {
        if (expr instanceof AtomExpr) {
            return visit((AtomExpr) expr);
        } else if (expr instanceof BinaryExpr) {
            return visit((BinaryExpr) expr);
        } else if (expr instanceof TernExpr) {
            return visit((TernExpr) expr);
        }

        return visit((UnaryExpr) expr);
    }

    @Override
    public Node visit(TernExpr ternExpr) {
        Expr condition = (Expr) visit(ternExpr.getCondition());
        Expr thenExpr = (Expr) visit(ternExpr.getThenExpr());
        Expr elseExpr = (Expr) visit(ternExpr.getElseExpr());

        return new TernExpr(condition, thenExpr, elseExpr);
    }

    @Override
    public Node visit(BinaryExpr binaryExpr) {
        String binaryOp = binaryExpr.getBinaryOp();
        Expr lhs = (Expr) visit(binaryExpr.getLhs());
        Expr rhs = (Expr) visit(binaryExpr.getRhs());

        return new BinaryExpr(binaryOp, lhs, rhs);
    }

    @Override
    public Node visit(UnaryExpr unaryExpr) {
        String unaryOp = unaryExpr.getUnaryOp();
        Expr arg = (Expr) visit(unaryExpr.getArg());

        return new UnaryExpr(unaryOp, arg);
    }

    @Override
    public Node visit(AtomExpr atomExpr) {
        if (atomExpr instanceof NumberExpr) {
            return visit((NumberExpr) atomExpr);
        } else if (atomExpr instanceof  OldExpr) {
            return visit((OldExpr) atomExpr);
        } else if (atomExpr instanceof ParenExpr) {
            return visit((ParenExpr) atomExpr);
        } else if (atomExpr instanceof ResultExpr) {
            return visit((ResultExpr) atomExpr);
        }

        return visit((VarRefExpr) atomExpr);
    }

    @Override
    public Node visit(NumberExpr numberExpr) {
        return new NumberExpr(numberExpr.getNumber());
    }

    @Override
    public Node visit(VarRefExpr varRefExpr) {
        return new VarRefExpr((VarRef) visit(varRefExpr.getVarRef()));
    }

    @Override
    public Node visit(ParenExpr parenExpr) {
        return new ParenExpr((Expr) visit(parenExpr.getExpr()));
    }

    @Override
    public Node visit(ResultExpr resultExpr) {
        return resultExpr;
    }

    @Override
    public Node visit(OldExpr oldExpr) {
        return new OldExpr((VarRef) visit(oldExpr.getVar()));
    }

    @Override
    public Node visit(VarRef varRef) {
        return new VarRef((VarIdentifier) visit(varRef.getVarIdentifier()));
    }

    @Override
    public Node visit(VarIdentifier varIdentifier) {
        return varIdentifier;
    }
}
