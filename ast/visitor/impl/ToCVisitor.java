package ast.visitor.impl;

import ast.*;
import tool.ScopesHandler;
import tool.VariableIdsGenerator;

import java.util.*;

public class ToCVisitor extends DefaultVisitor {

    private static final String GLOBAL_TEMP = "%scopy";

    private final Map<String, ProcedureDecl> methods;

    private List<String> globals;

    private Map<String, String> enclosingMethodGlobalsCopy;

    private ScopesHandler scopesHandler;

    public ToCVisitor(Map<Node, Node> predMap, Program program) {
        super(predMap);
        scopesHandler = new ScopesHandler(new VariableIdsGenerator());

        globals = new LinkedList<>();
        for (VarDecl varDecl: program.getVarDecls()) {
            globals.add(varDecl.getVarIdentifier().getVarName());
        }

        methods = new HashMap<>();
        for (ProcedureDecl procedureDecl: program.getProcedureDecls()) {
            methods.put(procedureDecl.getMethodName(), procedureDecl);
        }
    }

    private VarRef refForVar(String varName) {
        return new VarRef(new VarIdentifier(varName));
    }

    @Override
    public Object visit(ProcedureDecl procedureDecl) {
        scopesHandler.pushMethodsStack(procedureDecl);
        List<FormalParam> formalParams = new LinkedList<>();
        List<Stmt> stmts = new LinkedList<>();

        for (FormalParam param : procedureDecl.getParamList()) {
            formalParams.add((FormalParam) param.accept(this));
        }

        enclosingMethodGlobalsCopy = new HashMap<>();
        for (String global: globals) {
            String globalCopy = String.format(GLOBAL_TEMP, global);
            stmts.add(new VarDecl(new VarIdentifier(globalCopy)));
            stmts.add(new AssignStmt(refForVar(globalCopy), new VarRefExpr(refForVar(global))));
            enclosingMethodGlobalsCopy.put(global, globalCopy);
        }

        // add preconditions as assumes
        for (PrePostCondition prePostCondition : procedureDecl.getPrePostConditions()) {
            if (prePostCondition instanceof Precondition) {
                stmts.add(new AssumeStmt((Expr) prePostCondition.accept(this)));
            }
        }

        // method body
        for (Stmt stmt : procedureDecl.getStmts()) {
            stmts.add((Stmt) stmt.accept(this));
        }

        // add postconditions as asserts
        for (PrePostCondition prePostCondition : procedureDecl.getPrePostConditions()) {
            if (prePostCondition instanceof Postcondition) {
                AssertStmt assertPostCond = new AssertStmt((Expr) prePostCondition.accept(this));
                stmts.add(assertPostCond);
            }
        }

        // return expr
        Expr returnExpr = (Expr) procedureDecl.getReturnExpr().accept(this);

        scopesHandler.popMethodsStack();

        return new ProcedureDecl(procedureDecl.getMethodName(), formalParams, new LinkedList<>(), stmts, returnExpr);
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
    public Object visit(WhileStmt whileStmt) {
        Expr condition = (Expr) whileStmt.getCondition().accept(this);

        List<AssertStmt> invariantStmts = new LinkedList<>();
        // establish invariants hold on entry
        for (LoopInvariant invariant: whileStmt.getLoopInvariantList()) {
            if (invariant instanceof Invariant) {
                Invariant newInvariant = (Invariant) invariant.accept(this);
                AssertStmt assertInvariant = new AssertStmt(newInvariant.getCondition());
                invariantStmts.add(assertInvariant);
            }
        }

        BlockStmt body = (BlockStmt) whileStmt.getBody().accept(this);

        List<Stmt> stmtList = new LinkedList<>();
        // assert invariants
        stmtList.addAll(invariantStmts);

        List<Stmt> newWhileBodyStmts = new LinkedList<>();
        newWhileBodyStmts.add(body);
        newWhileBodyStmts.addAll(invariantStmts);
        BlockStmt newWhileBody = new BlockStmt(newWhileBodyStmts);
        // add new while (containing the required assertions)
        stmtList.add(new WhileStmt(condition, new LinkedList<>(), newWhileBody));

        return new BlockStmt(stmtList);
    }

    @Override
    public Object visit(OldExpr oldExpr) {
        String varName = oldExpr.getVar().getVarIdentifier().getVarName();
        return new VarRefExpr(refForVar(enclosingMethodGlobalsCopy.get(varName)));
    }

    @Override
    public Object visit(ResultExpr resultExpr) {
        return scopesHandler.getEnclosingMethod().getReturnExpr().accept(this);
    }
}
