package tool;


import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import parser.SimpleCBaseVisitor;
import parser.SimpleCParser;

import java.util.*;

class NodeResult {

    StringBuilder code;
    Set<String> modSet;
    // it's not quite sure what this is supposed to represent..
    // ideally it should be the mappings from modSet to actual integer
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

    // if the scope corresponds to a method scope, it must have a return statement
    // null if the scope is not a method scope
    // TODO(ccarabet): once a method starts to contain more logic, it might be a good idea to move this
    // into a special purpose method info class
    private SimpleCParser.ExprContext returnStmt = null;

    public ScopeInfo() {
        variables = new HashMap<>();
        conditions = new LinkedList<>();
    }

    public ScopeInfo(Map<String, Integer> variables) {
        this.variables = variables;
        this.conditions = new LinkedList<>();
    }

    public Map<String, Integer> getVariables() {
        return variables;
    }

    public List<String> getConditions() {
        return conditions;
    }

    public void addVariable(String name, Integer id) {
        variables.put(name, id);
    }

    public Integer getVariable(String name) {
        return variables.get(name);
    }

    public void addCondition(String cond) {
        conditions.add(cond);
    }

    public void setReturnStmt(SimpleCParser.ExprContext returnStmt) {
        this.returnStmt = returnStmt;
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

    private List<ScopeInfo> scopesStack = new LinkedList<>();

    private VariableIdsGenerator freshIds;

    public SimpleCToSSA(Map<String, Integer> globals, VariableIdsGenerator freshIds) {
        scopesStack.add(0, new ScopeInfo(globals));
        this.freshIds = freshIds;
    }

    // HELPER methods for scope related stuff - BEGIN

    private ScopeInfo peekScope() {
        return scopesStack.get(0);
    }

    private void popStack() {
        scopesStack.remove(0);
    }

    private void pushStack() {
        scopesStack.add(0, new ScopeInfo());
    }

    private void addVariableToScope(String name) {
        Integer newId = freshIds.generateFresh(name);
        peekScope().addVariable(name, newId);
    }

    private void addConditionToScope(String condition) {
        peekScope().addCondition(condition);
    }

    private void addReturnStmtToScope(SimpleCParser.ExprContext returnStmt) {
        peekScope().setReturnStmt(returnStmt);
    }

    String latestVarRef(String name) {
        for (ScopeInfo scope: scopesStack) {
            Integer valueForVar = scope.getVariable(name);
            if (valueForVar != null) {
                return String.format(VAR_ID, name, valueForVar);
            }
        }

        return null;
    }

    String getFromGivenScopeOrGlobal(ScopeInfo givenScope, String name) {
        Integer latestId = givenScope.getVariable(name);
        String result;
        if (latestId == null) {
            result = latestVarRef(name);
        } else {
            result = String.format(VAR_ID, name, latestId);
        }

        return result;
    }

    String getConditionsGlobal() {
        List<String> allConds = new ArrayList<>();
        for (ScopeInfo scope: scopesStack) {
            for (String cond: scope.getConditions()) {
                allConds.add(cond);
            }
        }
        String result = "";
        if (allConds.size() > 0) {
            result = allConds.get(0);
            for (int i = 1; i < allConds.size(); i++) {
                result = String.format("%s && %s", result, allConds.get(i));
            }
        }

        return result;
    }

    SimpleCParser.ExprContext getEnclosingrMethodReturnStmt() {
        for (ScopeInfo scope: scopesStack) {
            SimpleCParser.ExprContext returnStmt = scope.getReturnStmt();
            if (returnStmt != null) {
                return returnStmt;
            }
        }

        return null;
    }

    // HELPER methods for scope related stuff - END


    // HELPER methods for method related stuff - BEGIN

    /**
     * POST: obtain the precondition expressions for a method with the current mapping
      */
    private List<NodeResult> getPreconditionsForMethod(SimpleCParser.ProcedureDeclContext ctx) {
        List<NodeResult> result = new LinkedList<>();
        if (ctx.contract != null) {
            for (SimpleCParser.PrepostContext cond: ctx.contract) {
                if (cond.requires() != null) {
                    result.add(visit(cond.getChild(0)));
                }
            }
        }

        return result;
    }

    /**
     * POST: obtain the postcondition expressions for a method with the current mapping
     */
    private List<NodeResult> getPostconditionsForMethod(SimpleCParser.ProcedureDeclContext ctx) {
        List<NodeResult> result = new LinkedList<>();
        if (ctx.contract != null) {
            for (SimpleCParser.PrepostContext cond: ctx.contract) {
                if (cond.ensures() != null) {
                    result.add(visit(cond.getChild(0)));
                }
            }
        }

        return result;
    }

    // HELPER methods for method related stuff - END

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
        // add return stmt to scope so that postconditions can refer to it later
        addReturnStmtToScope(ctx.returnExpr);

        // add parameters on stack
        if (ctx.formals != null) {
            for (SimpleCParser.FormalParamContext param: ctx.formals) {
                addVariableToScope(param.ident.name.getText());
            }
        }
        // visit method body
        for (SimpleCParser.StmtContext stmt: ctx.stmt()) {
            NodeResult stmtResult = visit(stmt);
            code.append(stmtResult.getCode() + EOL);
            modSet.addAll(stmtResult.getModSet());
        }

        // add postconditions checks
        for (NodeResult cond: getPostconditionsForMethod(ctx)) {
            code.append(String.format(ASSERT_STMT, cond.getCode()) + EOL);
        }

        ScopeInfo scopeAfter = peekScope();
        popStack();

        String resultCode = String.format(PROGRAM, code);
        return new NodeResult(new StringBuilder(resultCode), modSet, scopeAfter);
    }

    @Override
    public NodeResult visitVarDecl(SimpleCParser.VarDeclContext ctx) {
        addVariableToScope(ctx.ident.name.getText());

        return new NodeResult();
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

        String condition = condExpr.getCode().toString();
        String allConditions = getConditionsGlobal();
        if (allConditions.length() > 0) {
            condition = String.format(IMPLICATION_STMT, allConditions, condition);
        }
        code.append(String.format(ASSERT_STMT, condition));
        return new NodeResult(code, new HashSet<>(), peekScope());
    }

    @Override
    public NodeResult visitBlockStmt(SimpleCParser.BlockStmtContext ctx) {
        StringBuilder code = new StringBuilder();
        Set<String> modSet = new HashSet<>();

        pushStack();
        for (SimpleCParser.StmtContext stmt: ctx.stmts) {
            NodeResult stmtResult = visit(stmt);
            if (stmtResult != null) {
                code.append(stmtResult.getCode() + EOL);
                modSet.addAll(stmtResult.getModSet());
            }
        }
        // scope at the end of block statement
        ScopeInfo scopeAfter = peekScope();
        popStack();

        return new NodeResult(code, modSet, scopeAfter);
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
            addConditionToScope(String.format("!%s", conditionResult.getCode().toString()));
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
            String newExpr = String.format("%s ? %s : %s", conditionResult.getCode().toString(), thenValue, elseValue);

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

        return new NodeResult(code, modSet, peekScope());
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

        return new NodeResult(code, modSet, peekScope());
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
        return null;
    }
}
