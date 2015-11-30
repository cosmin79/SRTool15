package ast.visitor.impl;

import ast.*;

import java.util.*;

public class MethodSummarisationVisitor extends DefaultVisitor {

    private static final String TEMP_RESULT = "%s_ret";

    private static final String TEMP_GLOBAL = "%s_temp";

    private final Program program;

    private final Map<String, ProcedureDecl> methods;

    private Set<String> globalVariables;

    private Map<String, Expr> enclosingCallParameters;

    private Map<String, String> oldGlobalsEnclosingCall;

    private String enclosingCallResult;

    boolean isInsideCallStmt;

    public MethodSummarisationVisitor(Map<Node, Node> pred, Program program) {
        super(pred);
        this.program = program;
        methods = new HashMap<>();
        for (ProcedureDecl procedureDecl: program.getProcedureDecls()) {
            methods.put(procedureDecl.getMethodName(), procedureDecl);
        }
        isInsideCallStmt = false;

        globalVariables = new HashSet<>();
        for (VarDecl varDecl: program.getVarDecls()) {
            globalVariables.add(varDecl.getVarIdentifier().getVarName());
        }
    }

    private VarRef refForName(String varName) {
        return new VarRef(new VarIdentifier(varName));
    }

    @Override
    public Object visit(CallStmt callStmt) {
        ProcedureDecl calleeMethod = methods.get(callStmt.getMethodName());
        String lhsVar = callStmt.getLhsVar().getVarIdentifier().getVarName();

        isInsideCallStmt = true;
        List<Stmt> stmtList = new LinkedList<>();

        List<Expr> parameters = new LinkedList<>();
        for (Expr expr: callStmt.getParametersList()) {
            parameters.add((Expr) expr.accept(this));
        }

        // create a mapping from expected parameters to call stmt provided arguments
        Iterator<Expr> paramsIterator = parameters.iterator();
        enclosingCallParameters = new HashMap<>();
        for (FormalParam formalParam: calleeMethod.getParamList()) {
            enclosingCallParameters.put(formalParam.getVarIdentifier().getVarName(), paramsIterator.next());
        }

        // set up copies after globals
        oldGlobalsEnclosingCall = new HashMap<>();
        for (String globalVar: globalVariables) {
            String globalVarTemp = String.format(TEMP_GLOBAL, globalVar);
            stmtList.add(new VarDecl(new VarIdentifier(globalVarTemp)));
            stmtList.add(new AssignStmt(refForName(globalVarTemp), new VarRefExpr(refForName(globalVar))));
            oldGlobalsEnclosingCall.put(globalVar, globalVarTemp);
        }

        // transform preconditions of callee into asserts
        for (PrePostCondition prePostCondition: calleeMethod.getPrePostConditions()) {
            if (prePostCondition instanceof Precondition) {
                Precondition newPrecondition = (Precondition) prePostCondition.accept(this);
                AssertStmt assertPrecond = new AssertStmt(newPrecondition.getCondition());
                predMap.put(assertPrecond, prePostCondition);
                stmtList.add(assertPrecond);
            }
        }

        // havoc modified set ; should only be applicable for global variables
        for (String modVar: calleeMethod.getModSet()) {
            if (globalVariables.contains(modVar)) {
                stmtList.add(new HavocStmt(refForName(modVar)));
            }
        }

        // introduce unused variable (note: this is a new variable because shadow visitor will add a number
        // at the end of each variable entry)
        enclosingCallResult = String.format(TEMP_RESULT, calleeMethod.getMethodName());
        stmtList.add(new VarDecl(new VarIdentifier(enclosingCallResult)));

        // transform postconditions of callee into assumes
        for (PrePostCondition prePostCondition: calleeMethod.getPrePostConditions()) {
            if (prePostCondition instanceof Postcondition) {
                Postcondition newPostcondition = (Postcondition) prePostCondition.accept(this);
                stmtList.add(new AssumeStmt(newPostcondition.getCondition()));
            }
        }
        stmtList.add(new AssignStmt(refForName(lhsVar), new VarRefExpr(refForName(enclosingCallResult))));
        isInsideCallStmt = false;

        return new BlockStmt(stmtList);
    }

    @Override
    public Object visit(VarRefExpr varRefExpr) {
        String varName = varRefExpr.getVarRef().getVarIdentifier().getVarName();
        if (isInsideCallStmt && enclosingCallParameters.containsKey(varName)) {
            return enclosingCallParameters.get(varName);
        }
        return super.visit(varRefExpr);
    }

    @Override
    public Object visit(ResultExpr resultExpr) {
        if (isInsideCallStmt) {
            return new VarRefExpr(refForName(enclosingCallResult));
        }
        return resultExpr;
    }

    @Override
    public Object visit(OldExpr oldExpr) {
        if (isInsideCallStmt) {
            String varName = oldExpr.getVar().getVarIdentifier().getVarName();
            return new VarRefExpr(refForName(oldGlobalsEnclosingCall.get(varName)));
        }
        return super.visit(oldExpr);
    }
}
