package tool;


import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import parser.SimpleCBaseVisitor;
import parser.SimpleCParser;

import java.util.*;

class NodeResult {

    StringBuilder code;
    Set<String> modSet;
    // this contains the local scope at the current node
    // this is useful for if statements when evaluating the then and else statement blocks
    // once the exploration of the 2 branches completes, this field can be used to recall how did their scope look like
    ScopeInfo latestScope;

    public NodeResult() {
        code = new StringBuilder();
        modSet = new HashSet<>();
        latestScope = new ScopeInfo();
    }

    public NodeResult(StringBuilder code, Set<String> modSet, ScopeInfo latestScope) {
        this.code = code;
        this.modSet = modSet;
        this.latestScope = latestScope;
    }

    public StringBuilder getCode() {
        return code;
    }

    public Set<String> getModSet() {
        return modSet;
    }
};

class ScopeInfo {

    private Map<String, Integer> variables;

    private List<String> conditions;

    public ScopeInfo() {
        variables = new HashMap<>();
        conditions = new LinkedList<>();
    }

    public ScopeInfo(Map<String, Integer> variables) {
        this.variables = variables;
        conditions = new LinkedList<>();
    }

    public Map<String, Integer> getVariables() {
        return variables;
    }

    public List<String> getConditions() {
        return conditions;
    }

    public Integer getVariable(String name) {
        return variables.get(name);
    }

    public void addVariable(String name, Integer id) {
        variables.put(name, id);
    }

    public void addCondition(String cond) {
        conditions.add(cond);
    }
}

class MethodScope {

    private SimpleCParser.ProcedureDeclContext procedureNode;

    private Map<String, Integer> globalsValue;

    private List<SimpleCParser.RequiresContext> preConditionsNodes;

    private List<SimpleCParser.EnsuresContext> postConditionsNodes;

    private SimpleCParser.ExprContext returnStmt;

    public MethodScope(SimpleCParser.ProcedureDeclContext ctx, Map<String, Integer> globalsValue) {
        procedureNode = ctx;
        this.globalsValue = globalsValue;
        returnStmt = ctx.returnExpr;
        preConditionsNodes = new LinkedList<>();
        postConditionsNodes = new LinkedList<>();

        for (SimpleCParser.PrepostContext cond: ctx.contract) {
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

    public List<SimpleCParser.RequiresContext> getPreConditionsNodes() {
        return preConditionsNodes;
    }

    public List<SimpleCParser.EnsuresContext> getPostConditionsNodes() {
        return postConditionsNodes;
    }

    public SimpleCParser.ExprContext getReturnStmt() {
        return returnStmt;
    }
}

/**
 * Pre: assumes the visiting starts from a node of type ProcedureDeclContext
 * Post: returns an equivalent program in Simple C, but in SSA form (only assignments and asserts)
 */
public class SimpleCToSSA extends SimpleCBaseVisitor<NodeResult> {

    private static final String EOL = "\n";

    private static final String ASSIGN_STMT = "%s=%s;\n";

    private static final String ASSERT_STMT = "assert %s;\n";

    private static final String PROGRAM = "int main() {\n%s\nreturn 0;\n}\n";

    private static final String VAR_ID = "%s%d";

    private static final String IMPLICATION_STMT = "!(%s) || %s";

    private List<String> globalVariables;

    private List<ScopeInfo> scopesStack;

    private List<MethodScope> methodScopesStack;

    private List<String> assumptions;

    private VariableIdsGenerator freshIds;

    public SimpleCToSSA(Map<String, Integer> globals, VariableIdsGenerator freshIds) {
        globalVariables = new LinkedList<>(globals.keySet());

        scopesStack = new LinkedList<>();
        scopesStack.add(0, new ScopeInfo(globals));

        this.freshIds = freshIds;
        methodScopesStack = new LinkedList<>();
        assumptions = new LinkedList<>();
    }

    // HELPER methods for scope related stuff - BEGIN
    private ScopeInfo peekScope() {
        return scopesStack.get(0);
    }

    private MethodScope peekMethodScope() {
        return methodScopesStack.get(0);
    }

    private void popStack() {
        scopesStack.remove(0);
    }

    private void popMethodsStack() {
        methodScopesStack.remove(0);
    }

    private void pushStack() {
        scopesStack.add(0, new ScopeInfo());
    }

    private void pushMethodStack(MethodScope method) {
        methodScopesStack.add(0, method);
    }

    private void addVariableToScope(String name) {
        Integer newId = freshIds.generateFresh(name);
        peekScope().addVariable(name, newId);
    }

    private void addConditionToScope(String condition) {
        peekScope().addCondition(condition);
    }

    private void addAssumption(String condition) {
        String conditionGlobals = getConditionsGlobal();
        if (!conditionGlobals.isEmpty()) {
            condition = String.format(IMPLICATION_STMT, getConditionsGlobal(), condition);
        }
        assumptions.add(condition);
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

    private String latestVarRef(String name) {
        Integer latestId = latestVarId(name);
        return latestId != null ? String.format(VAR_ID, name, latestId) : null;
    }

    private String getFromGivenScopeOrGlobal(ScopeInfo givenScope, String name) {
        Integer latestId = givenScope.getVariable(name);
        String result;
        if (latestId == null) {
            result = latestVarRef(name);
        } else {
            result = String.format(VAR_ID, name, latestId);
        }

        return result;
    }

    private String combineConditions(String cond1, String cond2) {
        if (cond1.isEmpty()) {
            return cond2;
        } else if (cond2.isEmpty()) {
            return cond1;
        }

        return String.format("%s && %s", cond1, cond2);
    }

    private String andConditions(List<String> conditions) {
        String result = "";
        for (String condition: conditions) {
            result = combineConditions(result, condition);
        }

        return result;
    }

    private String getConditionsGlobal() {
        List<String> allConds = new ArrayList<>();
        for (ScopeInfo scope: scopesStack) {
            for (String cond: scope.getConditions()) {
                allConds.add(cond);
            }
        }

        return andConditions(allConds);
    }

    private String getAssumptionsGlobal() {
        return andConditions(assumptions);
    }

    private String getGlobalAssertCondition(String condition) {
        String allConditions = combineConditions(getConditionsGlobal(), getAssumptionsGlobal());
        if (!allConditions.isEmpty()) {
            condition = String.format(IMPLICATION_STMT, allConditions, condition);
        }

        return String.format(ASSERT_STMT, condition);
    }

    private SimpleCParser.ExprContext getEnclosingrMethodReturnStmt() {
        return peekMethodScope().getReturnStmt();
    }

    private Map<String, Integer> globalsValueAtEntry() {
        Map<String, Integer> globalsValues = new HashMap<>();
        for (String globalVar: globalVariables) {
            globalsValues.put(globalVar, latestVarId(globalVar));
        }

        return globalsValues;
    }
    // HELPER methods for scope related stuff - END

    @Override
    public NodeResult visitEnsures(SimpleCParser.EnsuresContext ctx) {
        return visit(ctx.condition);
    }

    @Override
    public NodeResult visitRequires(SimpleCParser.RequiresContext ctx) {
        return visit(ctx.condition);
    }

    @Override
    public NodeResult visitProcedureDecl(SimpleCParser.ProcedureDeclContext ctx) {
        StringBuilder code = new StringBuilder();
        Set<String> modSet = new HashSet<>();

        pushStack();
        pushMethodStack(new MethodScope(ctx, globalsValueAtEntry()));

        // add parameters to current stack
        if (ctx.formals != null) {
            for (SimpleCParser.FormalParamContext param: ctx.formals) {
                addVariableToScope(param.ident.name.getText());
            }
        }

        // add preconditions
        for (SimpleCParser.RequiresContext assumption: peekMethodScope().getPreConditionsNodes()) {
            NodeResult assumptionExpr = visit(assumption);
            addAssumption(assumptionExpr.getCode().toString());
        }

        // visit method body
        for (SimpleCParser.StmtContext stmt: ctx.stmt()) {
            NodeResult stmtResult = visit(stmt);
            code.append(stmtResult.getCode() + EOL);
            modSet.addAll(stmtResult.getModSet());
        }

        // add postconditions
        for (SimpleCParser.EnsuresContext cond: peekMethodScope().getPostConditionsNodes()) {
            NodeResult ensuresExpr = visit(cond);
            code.append(getGlobalAssertCondition(ensuresExpr.getCode().toString()) + EOL);
        }

        ScopeInfo scopeAfter = peekScope();
        popStack();
        popMethodsStack();

        String resultCode = String.format(PROGRAM, code);
        return new NodeResult(new StringBuilder(resultCode), modSet, scopeAfter);
    }

    @Override
    public NodeResult visitVarDecl(SimpleCParser.VarDeclContext ctx) {
        String varName = ctx.ident.name.getText();
        addVariableToScope(varName);

        Set<String> modSet = new HashSet<>();
        modSet.add(varName);

        return new NodeResult(new StringBuilder(), modSet, peekScope());
    }

    @Override
    public NodeResult visitAssignStmt(SimpleCParser.AssignStmtContext ctx) {
        StringBuilder code = new StringBuilder();
        Set<String> modSet = new HashSet<>();

        // visit rhs expression before assigning it to a new variable
        NodeResult rhsResult = visit(ctx.rhs);
        // create new variable entry
        String name = ctx.lhs.ident.name.getText();
        addVariableToScope(name);
        code.append(String.format(ASSIGN_STMT, latestVarRef(name), rhsResult.getCode()));

        // update modSet
        modSet.addAll(rhsResult.modSet);
        modSet.add(name);

        return new NodeResult(code, modSet, peekScope());
    }

    @Override
    public NodeResult visitAssertStmt(SimpleCParser.AssertStmtContext ctx) {
        StringBuilder code = new StringBuilder();
        // obtain result of the underlying expression
        NodeResult condExpr = visit(ctx.condition);
        code.append(getGlobalAssertCondition(condExpr.getCode().toString()));

        return new NodeResult(code, new HashSet<>(), peekScope());
    }

    @Override
    public NodeResult visitHavocStmt(SimpleCParser.HavocStmtContext ctx) {
        String varName = ctx.var.ident.name.getText();
        addVariableToScope(varName);

        Set<String> modSet = new HashSet<>();
        modSet.add(varName);

        return new NodeResult(new StringBuilder(), modSet, peekScope());
    }

    @Override
    public NodeResult visitAssumeStmt(SimpleCParser.AssumeStmtContext ctx) {
        NodeResult cond = visit(ctx.condition);
        addAssumption(cond.getCode().toString());

        return new NodeResult(new StringBuilder(), cond.getModSet(), peekScope());
    }

    @Override
    public NodeResult visitBlockStmt(SimpleCParser.BlockStmtContext ctx) {
        StringBuilder code = new StringBuilder();
        Set<String> modSet = new HashSet<>();

        pushStack();
        for (SimpleCParser.StmtContext stmt: ctx.stmts) {
            NodeResult stmtResult = visit(stmt);
            code.append(stmtResult.getCode() + EOL);
            modSet.addAll(stmtResult.getModSet());
        }
        // scope at the end of block statement
        ScopeInfo scopeAfter = peekScope();
        popStack();

        return new NodeResult(code, modSet, scopeAfter);
    }

    private String generateNewIfValue(String cond, String thenValue, String elseValue) {
        // make sure the value is not null for the then and else cases
        thenValue = thenValue != null ? thenValue : elseValue;
        elseValue = elseValue != null ? elseValue : thenValue;

        return String.format("%s ? %s : %s", cond, thenValue, elseValue);
    }

    @Override
    public NodeResult visitIfStmt(SimpleCParser.IfStmtContext ctx) {
        NodeResult conditionResult = visit(ctx.condition);
        StringBuilder code = new StringBuilder();
        Set<String> modSet = new HashSet<>();

        // evaluate then branch
        pushStack();
        addConditionToScope(conditionResult.getCode().toString());
        NodeResult thenResult = visit(ctx.thenBlock);
        modSet.addAll(thenResult.getModSet());
        code.append(thenResult.getCode().toString());
        popStack();

        NodeResult elseResult = new NodeResult(new StringBuilder(), new HashSet<>(), peekScope());
        // evaluate else branch
        if (ctx.elseBlock != null) {
            pushStack();
            addConditionToScope(String.format("!(%s)", conditionResult.getCode().toString()));
            elseResult = visit(ctx.elseBlock);
            modSet.addAll(elseResult.getModSet());
            code.append(elseResult.getCode().toString());
            popStack();
        }

        // update modified variables
        for (String modifiedVar: modSet) {
            // get value of the variable from then branch
            String thenValue = getFromGivenScopeOrGlobal(thenResult.latestScope, modifiedVar);
            // get value from else branch
            String elseValue = getFromGivenScopeOrGlobal(elseResult.latestScope, modifiedVar);

            // new value of variable
            String newExpr = generateNewIfValue(conditionResult.getCode().toString(), thenValue, elseValue);

            // generate new label for variable
            addVariableToScope(modifiedVar);
            code.append(String.format(ASSIGN_STMT, latestVarRef(modifiedVar), newExpr));
        }

        return new NodeResult(code, modSet, peekScope());
    }

    @Override
    public NodeResult visitVarIdentifier(SimpleCParser.VarIdentifierContext ctx) {
        StringBuilder code = new StringBuilder();
        Set<String> modSet = new HashSet<>();

        String name = ctx.getText();
        code.append(latestVarRef(name));
        modSet.add(name);

        return new NodeResult(code, modSet, peekScope());
    }

    @Override
    public NodeResult visitVarref(SimpleCParser.VarrefContext ctx) {
        return visit(ctx.ident);
    }

    @Override
    public NodeResult visitExpr(SimpleCParser.ExprContext ctx) {
        return visit(ctx.ternExpr());
    }

    @Override
    public NodeResult visitTernExpr(SimpleCParser.TernExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }
        List<NodeResult> childrenResults = new ArrayList<>();
        for (SimpleCParser.LorExprContext child: ctx.args) {
            childrenResults.add(visit(child));
        }

        StringBuilder code = new StringBuilder(childrenResults.get(0).getCode());
        Set<String> modSet = new HashSet<>(childrenResults.get(0).getModSet());
        for (int i = 1; i < childrenResults.size(); i += 2) {
            NodeResult currChild = childrenResults.get(i);
            NodeResult nextChild = childrenResults.get(i + 1);
            code.append(String.format("? %s : %s ", currChild.getCode(), nextChild.getCode()));
            modSet.addAll(currChild.getModSet());
            modSet.addAll(nextChild.getModSet());
        }
        String result = String.format("(%s)", code.toString());

        return new NodeResult(new StringBuilder(result), modSet, peekScope());
    }

    /**
     * Processes an expression's children ; the expected general form of the expression is:
     *
     * child_1 sep_1 child_2 sep_2 ... sep_(n - 1) child_n
    **/
    private<T extends ParserRuleContext> NodeResult generateFromChildrenExpr(List<T> childrenCtx, List<Token> sep) {
        List<NodeResult> childrenResults = new ArrayList<>();
        for (T child: childrenCtx) {
            childrenResults.add(visit(child));
        }

        StringBuilder code = new StringBuilder(childrenResults.get(0).getCode());
        Set<String> modSet = new HashSet<>(childrenResults.get(0).getModSet());
        Iterator<Token> currToken = sep.iterator();
        for (int i = 1; i < childrenResults.size(); i++) {
            NodeResult currChild = childrenResults.get(i);
            code.append(String.format(" %s %s", currToken.next().getText(), currChild.getCode()));
            modSet.addAll(currChild.getModSet());
        }
        String result = String.format("(%s)", code.toString());

        return new NodeResult(new StringBuilder(result), modSet, peekScope());
    }

    @Override
    public NodeResult visitLorExpr(SimpleCParser.LorExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }
        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public NodeResult visitLandExpr(SimpleCParser.LandExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }
        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public NodeResult visitBorExpr(SimpleCParser.BorExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }
        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public NodeResult visitBxorExpr(SimpleCParser.BxorExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }
        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public NodeResult visitBandExpr(SimpleCParser.BandExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }
        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public NodeResult visitEqualityExpr(SimpleCParser.EqualityExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }
        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public NodeResult visitRelExpr(SimpleCParser.RelExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }
        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public NodeResult visitShiftExpr(SimpleCParser.ShiftExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }
        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public NodeResult visitAddExpr(SimpleCParser.AddExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }
        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public NodeResult visitMulExpr(SimpleCParser.MulExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }
        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public NodeResult visitUnaryExpr(SimpleCParser.UnaryExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        StringBuilder code = new StringBuilder();
        for (Token op: ctx.ops) {
            code.append(op.getText());
        }

        NodeResult child = visit(ctx.arg);
        code.append(child.getCode());
        Set<String> modSet = new HashSet<>(child.getModSet());

        return new NodeResult(code, modSet, peekScope());
    }

    @Override
    public NodeResult visitAtomExpr(SimpleCParser.AtomExprContext ctx) {
        // it does seem to have only one child
        return visit(ctx.getChild(0));
    }

    @Override
    public NodeResult visitNumberExpr(SimpleCParser.NumberExprContext ctx) {
        return new NodeResult(new StringBuilder(ctx.number.getText()), new HashSet<>(), peekScope());
    }

    @Override
    public NodeResult visitVarrefExpr(SimpleCParser.VarrefExprContext ctx) {
        return visit(ctx.var);
    }

    @Override
    public NodeResult visitParenExpr(SimpleCParser.ParenExprContext ctx) {
        NodeResult child = visit(ctx.arg);
        String newCode = String.format("(%s)", child.getCode());

        return new NodeResult(new StringBuilder(newCode), new HashSet<>(child.getModSet()), peekScope());
    }

    @Override
    public NodeResult visitResultExpr(SimpleCParser.ResultExprContext ctx) {
        return visit(getEnclosingrMethodReturnStmt());
    }

    @Override
    public NodeResult visitOldExpr(SimpleCParser.OldExprContext ctx) {
        String varName = ctx.arg.ident.name.getText();
        String newCode = String.format(VAR_ID, varName, peekMethodScope().getGlobalValueAtEntry(varName));

        return new NodeResult(new StringBuilder(newCode), new HashSet<>(), peekScope());
    }
}
