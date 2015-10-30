package tool;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import parser.SimpleCBaseVisitor;
import parser.SimpleCParser;

import java.util.*;

public class SimpleCToNoShadowing extends SimpleCBaseVisitor<String> {

    private static final String EOL = "\n";

    private static final String COMMA = ",";

    private static final String SPACE = " ";

    private static final String FORMAL_PARAM = "int %s";

    private static final String VAR_DECL = "int %s;\n";

    private static final String ASSIGN_STMT = "%s=%s;\n";

    private static final String ASSERT_STMT = "assert %s;\n";

    private static final String ASSUME_STMT = "assume %s;\n";

    private static final String BLOCK_STMT = "{\n%s}\n";

    private static final String HAVOC_STMT = "havoc %s;\n";

    private static final String IF_STMT = "if (%s) %s";

    private static final String IF_ELSE_STMT = "else %s";

    private static final String WHILE_STMT = "while (%s)\n %s %s";

    private static final String METHOD = "int %s(%s) %s{\n%s return %s;\n}\n";

    private static final String ENSURES = "ensures %s";

    private static final String CANDIDATE_ENSURES = "candidate_ensures %s";

    private static final String REQUIRES = "requires %s";

    private static final String CANDIDATE_REQUIRES = "candidate_requires %s";

    private static final String INVARIANT = "invariant %s";

    private static final String CANDIDATE_INVARIANT = "candidateInvariant %s";

    private static final String VAR_ID = "%s%d";

    private static final String CALL_STMT = "%s = %s(%s);\n";

    private static final String PAREN_EXPR = "(%s)";

    private static final String RESULT_EXPR = "\\result";

    private static final String OLD_EXPR = "\\old(%s)";

    private VariableIdsGenerator freshIds;

    private List<Map<String, Integer>> scopesStack;

    private List<Map<String, Integer>> methodsStack;

    private Map<String, Integer> globalVariables;

    public SimpleCToNoShadowing(VariableIdsGenerator freshIds) {
        this.freshIds = freshIds;
        scopesStack = new LinkedList<>();
        methodsStack = new LinkedList<>();
        globalVariables = new HashMap<>();
    }

    // HELPER methods BEGIN

    private void pushStack() {
        scopesStack.add(0, new HashMap<>());
    }

    private void popStack() {
        scopesStack.remove(0);
    }

    private Map<String, Integer> peekScope() {
        return scopesStack.get(0);
    }

    private void addVariableToScope(String name) {
        Integer newId = freshIds.generateFresh(name);
        peekScope().put(name, newId);
    }

    private Integer latestVarId(String name) {
        for (Map<String, Integer> scope: scopesStack) {
            Integer valueForVar = scope.get(name);
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
    // HELPER methods END

    @Override
    public String visitProgram(SimpleCParser.ProgramContext ctx) {
        StringBuilder code = new StringBuilder();
        pushStack();
        // add global variables
        for (SimpleCParser.VarDeclContext var: ctx.globals) {
            code.append(visit(var) + EOL);
            String globalVar = var.ident.name.getText();
            globalVariables.put(globalVar, latestVarId(globalVar));
        }

        // add methods
        for (SimpleCParser.ProcedureDeclContext proc: ctx.procedures) {
            code.append(visit(proc) + EOL);
        }
        popStack();

        return code.toString();
    }

    @Override
    public String visitVarDecl(SimpleCParser.VarDeclContext ctx) {
        String varName = ctx.ident.name.getText();
        addVariableToScope(varName);

        return String.format(VAR_DECL, latestVarRef(varName));
    }

    private<T extends ParserRuleContext> String tokenSeparated(List<T> listNodes, String sep) {
        StringBuilder code = new StringBuilder();
        if (listNodes != null && !listNodes.isEmpty()) {
            code.append(visit(listNodes.get(0)));
            for (int idx = 1; idx < listNodes.size(); idx++) {
                code.append(sep + " " + visit(listNodes.get(idx)));
            }
        }

        return code.toString();
    }

    @Override
    public String visitProcedureDecl(SimpleCParser.ProcedureDeclContext ctx) {
        pushStack();
        String methodName = ctx.name.getText();

        // obtain parameters string
        String parameters = tokenSeparated(ctx.formals, COMMA + SPACE);

        // obtain preconditions and postconditions string
        String prepost = tokenSeparated(ctx.contract, COMMA + SPACE);

        // obtain method body
        String stmts = tokenSeparated(ctx.stmts, "");

        // expression for return stmt
        String returnStmt = visit(ctx.returnExpr);
        popStack();

        return String.format(METHOD, methodName, parameters, prepost, stmts, returnStmt);
    }

    @Override
    public String visitFormalParam(SimpleCParser.FormalParamContext ctx) {
        String varName = ctx.ident.name.getText();
        addVariableToScope(varName);

        return String.format(FORMAL_PARAM, latestVarRef(varName));
    }

    @Override
    public String visitRequires(SimpleCParser.RequiresContext ctx) {
        return String.format(REQUIRES, visit(ctx.condition));
    }

    @Override
    public String visitEnsures(SimpleCParser.EnsuresContext ctx) {
        return String.format(ENSURES, visit(ctx.condition));
    }

    @Override
    public String visitCandidateRequires(SimpleCParser.CandidateRequiresContext ctx) {
        return String.format(CANDIDATE_REQUIRES, visit(ctx.condition));
    }

    @Override
    public String visitCandidateEnsures(SimpleCParser.CandidateEnsuresContext ctx) {
        return String.format(CANDIDATE_ENSURES, visit(ctx.condition));
    }

    @Override
    public String visitAssignStmt(SimpleCParser.AssignStmtContext ctx) {
        String rhsResult = visit(ctx.rhs);
        String name = ctx.lhs.ident.name.getText();

        return String.format(ASSIGN_STMT, latestVarRef(name), rhsResult);
    }

    @Override
    public String visitAssertStmt(SimpleCParser.AssertStmtContext ctx) {
        return String.format(ASSERT_STMT, visit(ctx.condition));
    }

    @Override
    public String visitAssumeStmt(SimpleCParser.AssumeStmtContext ctx) {
        return String.format(ASSUME_STMT, visit(ctx.condition));
    }

    @Override
    public String visitHavocStmt(SimpleCParser.HavocStmtContext ctx) {
        return String.format(HAVOC_STMT, visit(ctx.var));
    }

    @Override
    public String visitCallStmt(SimpleCParser.CallStmtContext ctx) {
        String methodName = ctx.callee.getText();
        String paramsString = tokenSeparated(ctx.actuals, COMMA + SPACE);
        String lhsExpr = visit(ctx.lhs);

        return String.format(CALL_STMT, lhsExpr, methodName, paramsString);
    }

    @Override
    public String visitIfStmt(SimpleCParser.IfStmtContext ctx) {
        String conditionResult = visit(ctx.condition);
        StringBuilder code = new StringBuilder();

        // evaluate then branch
        pushStack();
        code.append(String.format(IF_STMT, conditionResult, visit(ctx.thenBlock)));
        popStack();

        String elseResult = new String();
        // evaluate else branch
        if (ctx.elseBlock != null) {
            pushStack();
            elseResult = visit(ctx.elseBlock);
            code.append(String.format(IF_ELSE_STMT, elseResult));
            popStack();
        }

        return code.toString();
    }

    @Override
    public String visitWhileStmt(SimpleCParser.WhileStmtContext ctx) {
        String whileCond = visit(ctx.condition);
        String invariants = tokenSeparated(ctx.invariantAnnotations, COMMA + EOL);
        String body = visit(ctx.body);

        return String.format(WHILE_STMT, whileCond, invariants, body);
    }

    @Override
    public String visitBlockStmt(SimpleCParser.BlockStmtContext ctx) {
        StringBuilder code = new StringBuilder();

        pushStack();
        for (SimpleCParser.StmtContext stmt: ctx.stmts) {
            code.append(visit(stmt));
        }
        popStack();

        return String.format(BLOCK_STMT, code.toString());
    }

    @Override
    public String visitLoopInvariant(SimpleCParser.LoopInvariantContext ctx) {
        return visit(ctx.getChild(0));
    }

    @Override
    public String visitInvariant(SimpleCParser.InvariantContext ctx) {
        return String.format(INVARIANT, visit(ctx.condition));
    }

    @Override
    public String visitCandidateInvariant(SimpleCParser.CandidateInvariantContext ctx) {
        return String.format(CANDIDATE_INVARIANT, visit(ctx.condition));
    }

    @Override
    public String visitTernExpr(SimpleCParser.TernExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> childrenResults = new ArrayList<>();
        for (SimpleCParser.LorExprContext child: ctx.args) {
            childrenResults.add(visit(child));
        }

        StringBuilder code = new StringBuilder(childrenResults.get(0));
        for (int i = 1; i < childrenResults.size(); i += 2) {
            String currChild = childrenResults.get(i);
            String nextChild = childrenResults.get(i + 1);
            code.append(String.format("? %s : %s ", currChild, nextChild));
        }
        String result = String.format("%s", code.toString());

        return result;
    }

    /**
     * Processes an expression's children ; the expected general form of the expression is:
     *
     * child_1 sep_1 child_2 sep_2 ... sep_(n - 1) child_n
     **/
    private<T extends ParserRuleContext> String generateFromChildrenExpr(List<T> childrenCtx, List<Token> sep) {
        List<String> childrenResults = new ArrayList<>();
        for (T child: childrenCtx) {
            childrenResults.add(visit(child));
        }

        StringBuilder code = new StringBuilder(childrenResults.get(0));
        Iterator<Token> currToken = sep.iterator();
        for (int i = 1; i < childrenResults.size(); i++) {
            code.append(String.format(" %s %s", currToken.next().getText(), childrenResults.get(i)));
        }
        String result = String.format("%s", code.toString());

        return result;
    }

    @Override
    public String visitLorExpr(SimpleCParser.LorExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public String visitLandExpr(SimpleCParser.LandExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public String visitBorExpr(SimpleCParser.BorExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public String visitBxorExpr(SimpleCParser.BxorExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public String visitBandExpr(SimpleCParser.BandExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public String visitEqualityExpr(SimpleCParser.EqualityExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public String visitRelExpr(SimpleCParser.RelExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public String visitShiftExpr(SimpleCParser.ShiftExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public String visitAddExpr(SimpleCParser.AddExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public String visitMulExpr(SimpleCParser.MulExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public String visitUnaryExpr(SimpleCParser.UnaryExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        StringBuilder code = new StringBuilder();
        for (Token op: ctx.ops) {
            code.append(op.getText() + " ");
        }
        code.append(visit(ctx.arg));

        return code.toString();
    }

    @Override
    public String visitAtomExpr(SimpleCParser.AtomExprContext ctx) {
        return visit(ctx.getChild(0));
    }

    @Override
    public String visitNumberExpr(SimpleCParser.NumberExprContext ctx) {
        return ctx.number.getText();
    }

    @Override
    public String visitVarrefExpr(SimpleCParser.VarrefExprContext ctx) {
        return visit(ctx.var);
    }

    @Override
    public String visitParenExpr(SimpleCParser.ParenExprContext ctx) {
        return String.format(PAREN_EXPR, visit(ctx.arg));
    }

    @Override
    public String visitResultExpr(SimpleCParser.ResultExprContext ctx) {
        return RESULT_EXPR;
    }

    @Override
    public String visitOldExpr(SimpleCParser.OldExprContext ctx) {
        String varName = ctx.arg.ident.name.getText();
        String newOldVar = String.format(VAR_ID, ctx.arg.ident.name.getText(), globalVariables.get(varName));
        return String.format(OLD_EXPR, newOldVar);
    }

    @Override
    public String visitVarref(SimpleCParser.VarrefContext ctx) {
        return latestVarRef(ctx.ident.name.getText());
    }

    @Override
    public String visitVarIdentifier(SimpleCParser.VarIdentifierContext ctx) {
        return latestVarRef(ctx.name.getText());
    }
}
