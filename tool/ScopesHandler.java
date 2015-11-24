package tool;

import ast.*;

import java.util.*;

class ScopeInfo {

    private Map<String, Integer> variables;

    private Set<Expr> encounteredExprs;

    private Expr conditions;

    public ScopeInfo() {
        this(new HashMap<>());
    }

    public ScopeInfo(Map<String, Integer> variables) {
        this.variables = variables;
        conditions = NumberExpr.TRUE;
        encounteredExprs = new HashSet<>();
    }

    public Map<String, Integer> getVariables() {
        return variables;
    }

    public Expr getConditions() {
        return conditions;
    }

    public Integer getVariable(String name) {
        return variables.get(name);
    }

    public Set<Expr> getEncounteredExprs() {
        return encounteredExprs;
    }

    public void addVariable(String name, Integer id) {
        variables.put(name, id);
    }

    public void addCondition(Expr cond) {
        conditions = ScopesHandler.combineConditions(conditions, cond);
    }

    public void addExpr(Expr expr) {
        encounteredExprs.add(expr);
    }
}

class MethodScope {

    private Map<String, Integer> globalsValue;

    private ProcedureDecl procedureDecl;

    public MethodScope(ProcedureDecl procedureDecl, Map<String, Integer> globalsValue) {
        this.globalsValue = globalsValue;
        this.procedureDecl = procedureDecl;
    }

    public Integer getGlobalValueAtEntry(String varName) {
        return globalsValue.get(varName);
    }

    public ProcedureDecl getProcedureDecl() {
        return procedureDecl;
    }
}

public class ScopesHandler {

    private static final String VAR_ID = "%sa%d";

    private Set<String> globalVariables;

    private ScopeInfo globalScope;

    private List<ScopeInfo> scopesStack;

    private List<MethodScope> methodScopesStack;

    private Expr assumptions;

    private VariableIdsGenerator freshIds;

    public ScopesHandler(Map<String, Integer> globals, VariableIdsGenerator freshIds) {
        globalVariables = new HashSet<>(globals.keySet());
        scopesStack = new LinkedList<>();
        globalScope = new ScopeInfo(globals);
        scopesStack.add(0, globalScope);

        this.freshIds = freshIds;
        methodScopesStack = new LinkedList<>();
        assumptions = NumberExpr.TRUE;
    }

    public ScopesHandler(VariableIdsGenerator freshIds) {
        this(new HashMap<>(), freshIds);
    }

    private ScopeInfo peekScope() {
        return scopesStack.get(0);
    }

    private MethodScope peekMethodScope() {
        return methodScopesStack.get(0);
    }

    public ScopeInfo popStack() {
        return scopesStack.remove(0);
    }

    public void popMethodsStack() {
        methodScopesStack.remove(0);
    }

    public ScopeInfo pushStack() {
        scopesStack.add(0, new ScopeInfo());
        return peekScope();
    }

    public void pushMethodsStack(ProcedureDecl procedureDecl) {
        Map<String, Integer> globalsValues = new HashMap<>();
        for (String globalVar: globalVariables) {
            globalsValues.put(globalVar, latestVarId(globalVar));
        }

        methodScopesStack.add(0, new MethodScope(procedureDecl, globalsValues));
    }

    public Set<String> getGlobalVariables() {
        return globalVariables;
    }

    public void addVariable(String name) {
        Integer newId = freshIds.generateFresh(name);
        peekScope().addVariable(name, newId);
    }

    public void addGlobalVariable(String name) {
        globalScope.addVariable(name, freshIds.generateFresh(name));
        globalVariables.add(name);
    }

    public void addCondition(Expr condition) {
        peekScope().addCondition(condition);
    }

    public void addAssumption(Expr condition) {
        assumptions = combineConditions(assumptions, implicationCondition(getConditionsGlobal(), condition));
    }

    // TODO(ccarabet): give this method a better name or move this logic somewhere else.
    // this is only applicable for Houdini related logic
    public void addExpr(Expr expr) {
        if (expr.isCandidateHoudini()) {
            peekScope().addExpr(expr);
        }
    }

    private Integer latestVarId(String name) {
        for (ScopeInfo scope: scopesStack) {
            Integer valueForVar = scope.getVariable(name);
            if (valueForVar != null) {
                return valueForVar;
            }
        }

        return null;
    }

    public String latestVar(String name) {
        Integer latestId = latestVarId(name);
        return latestId != null ? String.format(VAR_ID, name, latestId) : null;
    }

    public String varFromGivenScopeOrGlobal(ScopeInfo givenScope, String name) {
        Integer latestId = givenScope.getVariable(name);

        return latestId != null ? String.format(VAR_ID, name, latestId) : latestVar(name);
    }

    public static Expr combineConditions(Expr cond1, Expr cond2) {
        return new BinaryExpr("&&", cond1, cond2);
    }

    public static Expr implicationCondition(Expr cond1, Expr cond2) {
        return new BinaryExpr("||", new UnaryExpr("!", cond1), cond2);
    }

    private Expr getConditionsGlobal() {
        Expr allConds = NumberExpr.TRUE;
        for (ScopeInfo scope: scopesStack) {
            allConds = combineConditions(allConds, scope.getConditions());
        }

        return allConds;
    }

    public ProcedureDecl getEnclosingMethod() {
        return peekMethodScope().getProcedureDecl();
    }

    public Expr generateCondition(Expr condition) {
        Expr allConditions = combineConditions(getConditionsGlobal(), assumptions);

        return implicationCondition(allConditions, condition);
    }

    public Integer getOldGlobalVariable(String varName) {
        return peekMethodScope().getGlobalValueAtEntry(varName);
    }

    public String getOldGlobal(String varName) {
        return String.format(VAR_ID, varName, getOldGlobalVariable(varName));
    }

    public Set<String> getDefinedVars() {
        Set<String> result = new HashSet<>();
        for (ScopeInfo scopeInfo: scopesStack) {
            result.addAll(scopeInfo.getVariables().keySet());
        }

        return result;
    }

    public Set<Expr> getUsedExprs() {
        Set<Expr> result = new HashSet<>();
        for (ScopeInfo scopeInfo: scopesStack) {
            result.addAll(scopeInfo.getEncounteredExprs());
        }

        return result;
    }
}
