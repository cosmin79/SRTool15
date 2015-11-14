package tool;

import ast.*;

import java.util.*;

class ScopeInfoNew {

    private Map<String, Integer> variables;

    private Expr conditions;

    public ScopeInfoNew() {
        this(new HashMap<>());
    }

    public ScopeInfoNew(Map<String, Integer> variables) {
        this.variables = variables;
        conditions = NumberExpr.TRUE;
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

    public void addVariable(String name, Integer id) {
        variables.put(name, id);
    }

    public void addCondition(Expr cond) {
        conditions = ScopesHandlerNew.combineConditions(conditions, cond);
    }
}

class MethodScopeNew {

    private Map<String, Integer> globalsValue;

    private ProcedureDecl procedureDecl;

    public MethodScopeNew(ProcedureDecl procedureDecl, Map<String, Integer> globalsValue) {
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

public class ScopesHandlerNew {

    private static final String VAR_ID = "%s%d";

    private Set<String> globalVariables;

    private ScopeInfoNew globalScope;

    private List<ScopeInfoNew> scopesStack;

    private List<MethodScopeNew> methodScopesStack;

    private Expr assumptions;

    private VariableIdsGenerator freshIds;

    public ScopesHandlerNew(Map<String, Integer> globals, VariableIdsGenerator freshIds) {
        globalVariables = new HashSet<>(globals.keySet());
        scopesStack = new LinkedList<>();
        globalScope = new ScopeInfoNew(globals);
        scopesStack.add(0, globalScope);

        this.freshIds = freshIds;
        methodScopesStack = new LinkedList<>();
        assumptions = NumberExpr.TRUE;
    }

    public ScopesHandlerNew(VariableIdsGenerator freshIds) {
        this(new HashMap<>(), freshIds);
    }

    private ScopeInfoNew peekScope() {
        return scopesStack.get(0);
    }

    private MethodScopeNew peekMethodScope() {
        return methodScopesStack.get(0);
    }

    public ScopeInfoNew popStack() {
        return scopesStack.remove(0);
    }

    public void popMethodsStack() {
        methodScopesStack.remove(0);
    }

    public void pushStack() {
        scopesStack.add(0, new ScopeInfoNew());
    }

    public void pushMethodsStack(ProcedureDecl procedureDecl) {
        Map<String, Integer> globalsValues = new HashMap<>();
        for (String globalVar: globalVariables) {
            globalsValues.put(globalVar, latestVarId(globalVar));
        }

        methodScopesStack.add(0, new MethodScopeNew(procedureDecl, globalsValues));
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

    private Integer latestVarId(String name) {
        for (ScopeInfoNew scope: scopesStack) {
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

    public String varFromGivenScopeOrGlobal(ScopeInfoNew givenScope, String name) {
        Integer latestId = givenScope.getVariable(name);

        return latestId != null ? String.format(VAR_ID, name, latestId) : latestVar(name);
    }

    public static Expr combineConditions(Expr cond1, Expr cond2) {
        if (cond1.equals(NumberExpr.TRUE)) {
            return cond2;
        } else if (cond2.equals(NumberExpr.TRUE)) {
            return cond1;
        } else if (cond1.equals(NumberExpr.FALSE) || cond2.equals(NumberExpr.FALSE)) {
            return NumberExpr.FALSE;
        }

        return new BinaryExpr("&&", cond1, cond2);
    }

    public static Expr implicationCondition(Expr cond1, Expr cond2) {
        if (cond1.equals(NumberExpr.TRUE)) {
            return cond2;
        } else if (cond2.equals(NumberExpr.FALSE)) {
            return cond1;
        }

        return new BinaryExpr("||", new UnaryExpr("!", cond1), cond2);
    }

    private Expr getConditionsGlobal() {
        Expr allConds = NumberExpr.TRUE;
        for (ScopeInfoNew scope: scopesStack) {
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
}
