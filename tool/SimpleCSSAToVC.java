package tool;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import parser.SimpleCBaseVisitor;
import parser.SimpleCParser;

import java.util.*;

enum ArgType {
    INT,
    BOOLEAN;
}

/**
 * We assume that this visitor is used for a SimpleC program with the following structure:
 *
 * int main() {
 *     <assignment> e.g. x1 = 2; </assignments>
 *     <asserts> e.g assert x == 2;</asserts>
 *     return 0;
 * }
 */
public class SimpleCSSAToVC extends SimpleCBaseVisitor<String> {

    private static final String EOL = "\n";

    private static final String ASSIGN_STMT = "(assert (= %s %s))\n";

    private static final String TRUE_EXPR = "(_ bv1 32)";

    private static final String AND_EXPR = "(and %s %s)";

    private static final String TO_BOOL_EXPR = "(tobool %s)";

    private static final String TO_INT_EXPR = "(tobv32 %s)";

    private static final String TERN_EXPR = "(ite (tobool %s) %s %s)";

    private static final String NUMBER = "(_ bv%s 32)";

    // mapping from a binary operator to the right SMT expression
    private final Map<String, String> operatorsMap = new HashMap<String, String>() {{
        put("||", "(or %s %s)");
        put("&&", "(and %s %s)");

        put("|", "(bvor %s %s)");
        put("^", "(bvxor %s %s)");
        put("&", "(bvand %s %s)");

        put("==", "(= %s %s)");
        put("!=", "(not (= %s %s))");

        put("<", "(bvslt %s %s)");
        put("<=", "(bvsle %s %s)");
        put(">", "(bvsgt %s %s)");
        put(">=", "(bvsge %s %s)");

        put("<<", "(bvshl %s %s)");
        put(">>", "(bvashr %s %s)");

        put("+", "(bvadd %s %s)");
        put("-", "(bvsub %s %s)");

        put("*", "(bvmul %s %s)");
        put("/", "(bvdiv %s %s)");
        put("%", "(bvsrem %s %s)");
    }};

    private static final Map<String, String> unaryOperatorsMap = new HashMap<String, String>() {{
        put("+", "%s");
        put("-", "(bvneg %s)");
        put("!", String.format(TO_INT_EXPR, String.format("(not %s)", TO_BOOL_EXPR)));
        put("~", "(bvnot %s)");
    }};
    // operators to expressions END

    private List<String> assertConditions;

    public SimpleCSSAToVC() {
        assertConditions = new ArrayList<>();
        assertConditions.add(TRUE_EXPR);
    }

    @Override
    public String visitProgram(SimpleCParser.ProgramContext ctx) {
        assert (ctx.procedures.size() == 1);

        StringBuilder code = new StringBuilder();
        for (SimpleCParser.ProcedureDeclContext proc: ctx.procedures) {
            code.append(visit(proc) + EOL);
        }

        if (!assertConditions.isEmpty()) {
            String andAssertions = String.format(TO_BOOL_EXPR, assertConditions.get(0));
            for (int i = 1; i < assertConditions.size(); i++) {
                String nextAssert = String.format(TO_BOOL_EXPR, assertConditions.get(i));
                andAssertions = String.format(AND_EXPR, andAssertions, nextAssert);
            }
            code.append(String.format("(assert (not %s))", andAssertions) + EOL);
        }


        return code.toString();
    }

    @Override
    public String visitProcedureDecl(SimpleCParser.ProcedureDeclContext ctx) {
        StringBuilder code = new StringBuilder();
        for (SimpleCParser.StmtContext stmt: ctx.stmt()) {
            code.append(visit(stmt));
        }

        return code.toString();
    }

    @Override
    public String visitAssignStmt(SimpleCParser.AssignStmtContext ctx) {
        String name = ctx.lhs.ident.name.getText();
        String rhsExpr = visit(ctx.rhs);

        return String.format(ASSIGN_STMT, name, rhsExpr);
    }

    @Override
    public String visitAssertStmt(SimpleCParser.AssertStmtContext ctx) {
        // we are collecting assert conditions to generate at the end a
        // big assert formula i.e. assert(! (c1 && c2 && ... && cN))
        assertConditions.add(visit(ctx.condition));

        return "";
    }

    @Override
    public String visitBlockStmt(SimpleCParser.BlockStmtContext ctx) {
        StringBuilder code = new StringBuilder();
        for (SimpleCParser.StmtContext stmt: ctx.stmts) {
            code.append(visit(stmt) + EOL);
        }

        return code.toString();
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

        Collections.reverse(childrenResults);
        String rhsChild = childrenResults.get(0);
        for (int i = 1; i < childrenResults.size(); i += 2) {
            String lhsChild = childrenResults.get(i);
            String condChild = childrenResults.get(i + 1);
            rhsChild = String.format(TERN_EXPR, condChild, lhsChild, rhsChild);
        }

        return rhsChild;
    }

    private String castFromTo(String expr, ArgType from, ArgType to) {
        if (from == to) {
            return expr;
        } else if (to == ArgType.BOOLEAN) {
            return String.format(TO_BOOL_EXPR, expr);
        }

        return String.format(TO_INT_EXPR, expr);
    }

    /**
     *
     * @param nodes list of expression nodes f
     * @param tokens a list of operators in the form of tokens to be applied in order for the given expressions
     * @param opArgsType expected arguments type (int or bool) for the binary operation
     * @param opRetType the type (int or bool) the binary expression returns
     * @param <T> expression type
     * @return an integer expression containing the given operator applied between every 2 consecutive expressions
     */
    private<T extends ParserRuleContext> String processBinaryExpr(List<T> nodes, List<Token> tokens,
                                                                  ArgType opArgsType, ArgType opRetType) {
        List<String> childrenResults = new ArrayList<>();
        for (T child: nodes) {
            childrenResults.add(visit(child));
        }

        String result = castFromTo(childrenResults.get(0), ArgType.INT, opArgsType);
        Iterator<Token> currToken = tokens.iterator();
        for (int idx = 1; idx < childrenResults.size(); idx++) {
            String binaryExpr = operatorsMap.get(currToken.next().getText());
            String nextChild = castFromTo(childrenResults.get(idx), ArgType.INT, opArgsType);
            result = castFromTo(String.format(binaryExpr, result, nextChild), opRetType, opArgsType);
        }

        return castFromTo(result, opArgsType, ArgType.INT);
    }

    @Override
    public String visitLorExpr(SimpleCParser.LorExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        return processBinaryExpr(ctx.args, ctx.ops, ArgType.BOOLEAN, ArgType.BOOLEAN);
    }

    @Override
    public String visitLandExpr(SimpleCParser.LandExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        return processBinaryExpr(ctx.args, ctx.ops, ArgType.BOOLEAN, ArgType.BOOLEAN);
    }

    @Override
    public String visitBorExpr(SimpleCParser.BorExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        return processBinaryExpr(ctx.args, ctx.ops, ArgType.INT, ArgType.INT);
    }

    @Override
    public String visitBxorExpr(SimpleCParser.BxorExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        return processBinaryExpr(ctx.args, ctx.ops, ArgType.INT, ArgType.INT);
    }

    @Override
    public String visitBandExpr(SimpleCParser.BandExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        return processBinaryExpr(ctx.args, ctx.ops, ArgType.INT, ArgType.INT);
    }

    @Override
    public String visitEqualityExpr(SimpleCParser.EqualityExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        return processBinaryExpr(ctx.args, ctx.ops, ArgType.INT, ArgType.BOOLEAN);
    }

    @Override
    public String visitRelExpr(SimpleCParser.RelExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        return processBinaryExpr(ctx.args, ctx.ops, ArgType.INT, ArgType.BOOLEAN);
    }

    @Override
    public String visitShiftExpr(SimpleCParser.ShiftExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        return processBinaryExpr(ctx.args, ctx.ops, ArgType.INT, ArgType.INT);
    }

    @Override
    public String visitAddExpr(SimpleCParser.AddExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        return processBinaryExpr(ctx.args, ctx.ops, ArgType.INT, ArgType.INT);
    }

    @Override
    public String visitMulExpr(SimpleCParser.MulExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        return processBinaryExpr(ctx.args, ctx.ops, ArgType.INT, ArgType.INT);
    }

    @Override
    public String visitUnaryExpr(SimpleCParser.UnaryExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        String expr = visit(ctx.arg);
        // apply the unary operators right to left
        Collections.reverse(ctx.ops);
        for (Token op: ctx.ops) {
            String unaryExpr = unaryOperatorsMap.get(op.getText());
            expr = String.format(unaryExpr, expr);
        }

        return expr;
    }

    @Override
    public String visitNumberExpr(SimpleCParser.NumberExprContext ctx) {
        return String.format(NUMBER, ctx.number.getText());
    }

    @Override
    public String visitVarrefExpr(SimpleCParser.VarrefExprContext ctx) {
        return visit(ctx.var);
    }

    @Override
    public String visitParenExpr(SimpleCParser.ParenExprContext ctx) {
        return visit(ctx.arg);
    }

    @Override
    public String visitVarref(SimpleCParser.VarrefContext ctx) {
        return visit(ctx.ident);
    }

    @Override
    public String visitVarIdentifier(SimpleCParser.VarIdentifierContext ctx) {
        return ctx.name.getText();
    }
}
