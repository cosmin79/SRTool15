package tool;

import parser.SimpleCParser.*;

import java.util.*;

import static tool.ScopesHandler.combineConditions;

class ScopeInfo {

    private Map<String, Integer> variables;

    private String conditions;

    public ScopeInfo() {
        variables = new HashMap<>();
        conditions = new String();
    }

    public ScopeInfo(Map<String, Integer> variables) {
        this.variables = variables;
        conditions = new String();
    }

    public Map<String, Integer> getVariables() {
        return variables;
    }

    public String getConditions() {
        return conditions;
    }

    public Integer getVariable(String name) {
        return variables.get(name);
    }

    public void addVariable(String name, Integer id) {
        variables.put(name, id);
    }

    public void addCondition(String cond) {
        conditions = combineConditions(conditions, cond);
    }
}

class MethodScope {

    private Map<String, Integer> globalsValue;

    private List<RequiresContext> preConditionsNodes;

    private List<EnsuresContext> postConditionsNodes;

    private ExprContext returnStmt;

    public MethodScope(ProcedureDeclContext ctx, Map<String, Integer> globalsValue) {
        this.globalsValue = globalsValue;
        returnStmt = ctx.returnExpr;
        preConditionsNodes = new LinkedList<>();
        postConditionsNodes = new LinkedList<>();

        for (PrepostContext cond: ctx.contract) {
            if (cond.requires() != null) {
                preConditionsNodes.add(cond.requires());
            } else if (cond.ensures() != null) {
                postConditionsNodes.add(cond.ensures());
            }
        }
    }

    public Integer getGlobalValueAtEntry(String varName) {
        return globalsValue.get(varName);
    }

    public List<RequiresContext> getPreConditionsNodes() {
        return preConditionsNodes;
    }

    public List<EnsuresContext> getPostConditionsNodes() {
        return postConditionsNodes;
    }

    public ExprContext getReturnStmt() {
        return returnStmt;
    }
}

public class ScopesHandler {

    private static final String VAR_ID = "%s%d";

    private static final String IMPLICATION_STMT = "!(%s) || %s";

    private Set<String> globalVariables;

    private ScopeInfo globalScope;

    private List<ScopeInfo> scopesStack;

    private List<MethodScope> methodScopesStack;

    private String assumptions;

    private VariableIdsGenerator freshIds;

    public ScopesHandler(Map<String, Integer> globals, VariableIdsGenerator freshIds) {
        globalVariables = new HashSet<>(globals.keySet());
        scopesStack = new LinkedList<>();
        globalScope = new ScopeInfo(globals);
        scopesStack.add(0, globalScope);

        this.freshIds = freshIds;
        methodScopesStack = new LinkedList<>();
        assumptions = new String();
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

    public void pushStack() {
        scopesStack.add(0, new ScopeInfo());
    }

    public void pushMethodsStack(ProcedureDeclContext ctx) {
        Map<String, Integer> globalsValues = new HashMap<>();
        for (String globalVar: globalVariables) {
            globalsValues.put(globalVar, latestVarId(globalVar));
        }

        methodScopesStack.add(0, new MethodScope(ctx, globalsValues));
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

    public void addCondition(String condition) {
        peekScope().addCondition(condition);
    }

    public void addAssumption(String condition) {
        String conditionGlobals = getConditionsGlobal();
        if (!conditionGlobals.isEmpty()) {
            condition = String.format(IMPLICATION_STMT, getConditionsGlobal(), condition);
        }

        assumptions = combineConditions(assumptions, condition);
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

    public static String combineConditions(String cond1, String cond2) {
        if (cond1.isEmpty()) {
            return cond2;
        } else if (cond2.isEmpty()) {
            return cond1;
        }

        return String.format("%s && %s", cond1, cond2);
    }

    private String getConditionsGlobal() {
        String allConds = new String();
        for (ScopeInfo scope: scopesStack) {
            allConds = combineConditions(allConds, scope.getConditions());
        }

        return allConds;
    }

    public String generateCondition(String condition) {
        String allConditions = combineConditions(getConditionsGlobal(), assumptions);
        if (!allConditions.isEmpty()) {
            condition = String.format(IMPLICATION_STMT, allConditions, condition);
        }

        return condition;
    }

    public List<RequiresContext> getEnclosingMethodPreconditions() {
        return peekMethodScope().getPreConditionsNodes();
    }

    public List<EnsuresContext> getEnclosingMethodPostconditions() {
        return peekMethodScope().getPostConditionsNodes();
    }

    public ExprContext getEnclosingMethodReturnStmt() {
        return peekMethodScope().getReturnStmt();
    }

    public Integer getOldGlobalVariable(String varName) {
        return peekMethodScope().getGlobalValueAtEntry(varName);
    }
}
