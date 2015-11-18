package ast.visitor.impl;

import ast.*;
import tool.ScopesHandler;
import tool.VariableIdsGenerator;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;

public class ShadowVisitor extends DefaultVisitor {

    private ScopesHandler scopesHandler;

    public ShadowVisitor(Map<Node, Node> predMap, Program program) {
        super(predMap);
        scopesHandler = new ScopesHandler(new VariableIdsGenerator());
        for (VarDecl varDecl: program.getVarDecls()) {
            scopesHandler.addGlobalVariable(varDecl.getVarIdentifier().getVarName());
        }
    }

    @Override
    public Object visit(Program program) {
        scopesHandler.pushStack();

        List<VarDecl> globals = new LinkedList<>();
        List<ProcedureDecl> procedures = new LinkedList<>();

        for (String globalVar: scopesHandler.getGlobalVariables()) {
            globals.add(new VarDecl(new VarIdentifier(scopesHandler.latestVar(globalVar))));
        }

        for (ProcedureDecl procedureDecl: program.getProcedureDecls()) {
            procedures.add((ProcedureDecl) procedureDecl.accept(this));
        }

        scopesHandler.popStack();

        return new Program(globals, procedures);
    }

    @Override
    public Object visit(ProcedureDecl procedureDecl) {
        scopesHandler.pushStack();
        scopesHandler.pushMethodsStack(procedureDecl);

        Object result = super.visit(procedureDecl);

        scopesHandler.popStack();
        scopesHandler.popMethodsStack();

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
    public Object visit(IfStmt ifStmt) {
        Expr condition = (Expr) ifStmt.getCondition().accept(this);

        scopesHandler.pushStack();
        BlockStmt thenBlock = (BlockStmt) ifStmt.getThenBlock().accept(this);
        scopesHandler.popStack();

        scopesHandler.pushStack();
        BlockStmt elseBlock = (BlockStmt) ifStmt.getElseBlock().accept(this);
        scopesHandler.popStack();

        return new IfStmt(condition, thenBlock, elseBlock);
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

    @Override
    public Object visit(OldExpr oldExpr) {
        String oldVarName = scopesHandler.getOldGlobal(oldExpr.getVar().getVarIdentifier().getVarName());

        return new OldExpr(new VarRef(new VarIdentifier(oldVarName)));
    }

    @Override
    public Object visit(VarIdentifier varIdentifier) {
        return new VarIdentifier(scopesHandler.latestVar(varIdentifier.getVarName()));
    }
}
