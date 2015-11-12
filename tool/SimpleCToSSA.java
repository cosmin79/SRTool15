package tool;


import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import parser.SimpleCBaseVisitor;
import parser.SimpleCParser.*;

import java.util.*;

class NodeResult {

    StringBuilder code;
    Set<String> modSet;

    public NodeResult() {
        code = new StringBuilder();
        modSet = new HashSet<>();
    }

    public NodeResult(StringBuilder code, Set<String> modSet) {
        this.code = code;
        this.modSet = modSet;
    }

    public StringBuilder getCode() {
        return code;
    }

    public Set<String> getModSet() {
        return modSet;
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

    private ScopesHandler scopesHandler;

    public SimpleCToSSA(Map<String, Integer> globals, VariableIdsGenerator freshIds) {
        scopesHandler = new ScopesHandler(globals, freshIds);
    }

    @Override
    public NodeResult visitEnsures(EnsuresContext ctx) {
        return visit(ctx.condition);
    }

    @Override
    public NodeResult visitRequires(RequiresContext ctx) {
        return visit(ctx.condition);
    }

    @Override
    public NodeResult visitProcedureDecl(ProcedureDeclContext ctx) {
        StringBuilder code = new StringBuilder();
        Set<String> modSet = new HashSet<>();

        scopesHandler.pushStack();
        scopesHandler.pushMethodsStack(ctx);

        // add parameters to current stack
        if (ctx.formals != null) {
            for (FormalParamContext param: ctx.formals) {
                scopesHandler.addVariable(param.ident.name.getText());
            }
        }

        // add preconditions
        for (RequiresContext assumption: scopesHandler.getEnclosingMethodPreconditions()) {
            NodeResult assumptionExpr = visit(assumption);
            scopesHandler.addAssumption(assumptionExpr.getCode().toString());
        }

        // visit method body
        for (StmtContext stmt: ctx.stmt()) {
            NodeResult stmtResult = visit(stmt);
            code.append(stmtResult.getCode() + EOL);
            modSet.addAll(stmtResult.getModSet());
        }

        // add postconditions
        for (EnsuresContext cond: scopesHandler.getEnclosingMethodPostconditions()) {
            NodeResult ensuresExpr = visit(cond);
            code.append(String.format(ASSERT_STMT,
                    scopesHandler.generateCondition(ensuresExpr.getCode().toString())));
        }

        scopesHandler.popStack();
        scopesHandler.popMethodsStack();

        String resultCode = String.format(PROGRAM, code);
        return new NodeResult(new StringBuilder(resultCode), modSet);
    }

    @Override
    public NodeResult visitVarDecl(VarDeclContext ctx) {
        String varName = ctx.ident.name.getText();
        scopesHandler.addVariable(varName);

        Set<String> modSet = new HashSet<>();
        modSet.add(varName);

        return new NodeResult(new StringBuilder(), modSet);
    }

    @Override
    public NodeResult visitAssignStmt(AssignStmtContext ctx) {
        StringBuilder code = new StringBuilder();
        Set<String> modSet = new HashSet<>();

        // visit rhs expression before assigning it to a new variable
        NodeResult rhsResult = visit(ctx.rhs);
        // create new variable entry
        String name = ctx.lhs.ident.name.getText();
        scopesHandler.addVariable(name);
        code.append(String.format(ASSIGN_STMT, scopesHandler.latestVar(name), rhsResult.getCode()));

        // update modSet
        modSet.addAll(rhsResult.modSet);
        modSet.add(name);

        return new NodeResult(code, modSet);
    }

    @Override
    public NodeResult visitAssertStmt(AssertStmtContext ctx) {
        StringBuilder code = new StringBuilder();
        // obtain result of the underlying expression
        NodeResult condExpr = visit(ctx.condition);
        code.append(String.format(ASSERT_STMT, scopesHandler.generateCondition(condExpr.getCode().toString())));

        return new NodeResult(code, new HashSet<>());
    }

    @Override
    public NodeResult visitHavocStmt(HavocStmtContext ctx) {
        String varName = ctx.var.ident.name.getText();
        scopesHandler.addVariable(varName);

        Set<String> modSet = new HashSet<>();
        modSet.add(varName);

        return new NodeResult(new StringBuilder(), modSet);
    }

    @Override
    public NodeResult visitAssumeStmt(AssumeStmtContext ctx) {
        NodeResult cond = visit(ctx.condition);
        scopesHandler.addAssumption(cond.getCode().toString());

        return new NodeResult(new StringBuilder(), cond.getModSet());
    }

    @Override
    public NodeResult visitBlockStmt(BlockStmtContext ctx) {
        StringBuilder code = new StringBuilder();
        Set<String> modSet = new HashSet<>();

        for (StmtContext stmt: ctx.stmts) {
            NodeResult stmtResult = visit(stmt);
            code.append(stmtResult.getCode() + EOL);
            modSet.addAll(stmtResult.getModSet());
        }

        return new NodeResult(code, modSet);
    }

    private String generateNewIfValue(String cond, String thenValue, String elseValue) {
        // make sure the value is not null for the then and else cases
        thenValue = thenValue != null ? thenValue : elseValue;
        elseValue = elseValue != null ? elseValue : thenValue;

        return String.format("%s ? %s : %s", cond, thenValue, elseValue);
    }

    @Override
    public NodeResult visitIfStmt(IfStmtContext ctx) {
        NodeResult conditionResult = visit(ctx.condition);
        StringBuilder code = new StringBuilder();
        Set<String> modSet = new HashSet<>();

        // evaluate then branch
        scopesHandler.pushStack();
        scopesHandler.addCondition(conditionResult.getCode().toString());
        NodeResult thenResult = visit(ctx.thenBlock);
        modSet.addAll(thenResult.getModSet());
        code.append(thenResult.getCode().toString());
        ScopeInfo thenScope = scopesHandler.popStack();

        NodeResult elseResult = new NodeResult(new StringBuilder(), new HashSet<>());
        ScopeInfo elseScope = new ScopeInfo();
        // evaluate else branch
        if (ctx.elseBlock != null) {
            scopesHandler.pushStack();
            scopesHandler.addCondition(String.format("!(%s)", conditionResult.getCode().toString()));
            elseResult = visit(ctx.elseBlock);
            modSet.addAll(elseResult.getModSet());
            code.append(elseResult.getCode().toString());
            elseScope = scopesHandler.popStack();
        }

        // update modified variables
        for (String modifiedVar: modSet) {
            // get value of the variable from then branch
            String thenValue = scopesHandler.varFromGivenScopeOrGlobal(thenScope, modifiedVar);
            // get value from else branch
            String elseValue = scopesHandler.varFromGivenScopeOrGlobal(elseScope, modifiedVar);

            // new value of variable
            String newExpr = generateNewIfValue(conditionResult.getCode().toString(), thenValue, elseValue);

            // generate new label for variable
            scopesHandler.addVariable(modifiedVar);
            code.append(String.format(ASSIGN_STMT, scopesHandler.latestVar(modifiedVar), newExpr));
        }

        return new NodeResult(code, modSet);
    }

    @Override
    public NodeResult visitVarIdentifier(VarIdentifierContext ctx) {
        StringBuilder code = new StringBuilder();
        code.append(scopesHandler.latestVar(ctx.getText()));

        return new NodeResult(code, new HashSet<>());
    }

    @Override
    public NodeResult visitVarref(VarrefContext ctx) {
        return visit(ctx.ident);
    }

    @Override
    public NodeResult visitExpr(ExprContext ctx) {
        return visit(ctx.ternExpr());
    }

    @Override
    public NodeResult visitTernExpr(TernExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }
        List<NodeResult> childrenResults = new ArrayList<>();
        for (LorExprContext child: ctx.args) {
            childrenResults.add(visit(child));
        }

        StringBuilder code = new StringBuilder(childrenResults.get(0).getCode());
        for (int i = 1; i < childrenResults.size(); i += 2) {
            NodeResult currChild = childrenResults.get(i);
            NodeResult nextChild = childrenResults.get(i + 1);
            code.append(String.format("? %s : %s ", currChild.getCode(), nextChild.getCode()));
        }
        String result = String.format("(%s)", code.toString());

        return new NodeResult(new StringBuilder(result), new HashSet<>());
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
        Iterator<Token> currToken = sep.iterator();
        for (int i = 1; i < childrenResults.size(); i++) {
            NodeResult currChild = childrenResults.get(i);
            code.append(String.format(" %s %s", currToken.next().getText(), currChild.getCode()));
        }
        String result = String.format("(%s)", code.toString());

        return new NodeResult(new StringBuilder(result), new HashSet<>());
    }

    @Override
    public NodeResult visitLorExpr(LorExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }
        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public NodeResult visitLandExpr(LandExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }
        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public NodeResult visitBorExpr(BorExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }
        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public NodeResult visitBxorExpr(BxorExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }
        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public NodeResult visitBandExpr(BandExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }
        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public NodeResult visitEqualityExpr(EqualityExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }
        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public NodeResult visitRelExpr(RelExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }
        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public NodeResult visitShiftExpr(ShiftExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }
        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public NodeResult visitAddExpr(AddExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }
        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public NodeResult visitMulExpr(MulExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }
        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public NodeResult visitUnaryExpr(UnaryExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        StringBuilder code = new StringBuilder();
        for (Token op: ctx.ops) {
            code.append(op.getText() + " ");
        }

        NodeResult child = visit(ctx.arg);
        code.append(child.getCode());

        return new NodeResult(code, new HashSet<>());
    }

    @Override
    public NodeResult visitNumberExpr(NumberExprContext ctx) {
        return new NodeResult(new StringBuilder(ctx.number.getText()), new HashSet<>());
    }

    @Override
    public NodeResult visitVarrefExpr(VarrefExprContext ctx) {
        return visit(ctx.var);
    }

    @Override
    public NodeResult visitParenExpr(ParenExprContext ctx) {
        NodeResult child = visit(ctx.arg);
        String newCode = String.format("(%s)", child.getCode());

        return new NodeResult(new StringBuilder(newCode), new HashSet<>());
    }

    @Override
    public NodeResult visitResultExpr(ResultExprContext ctx) {
        return visit(scopesHandler.getEnclosingMethodReturnStmt());
    }

    @Override
    public NodeResult visitOldExpr(OldExprContext ctx) {
        String varName = ctx.arg.ident.name.getText();
        String newCode = String.format(VAR_ID, varName, scopesHandler.getOldGlobalVariable(varName));

        return new NodeResult(new StringBuilder(newCode), new HashSet<>());
    }
}
