package tool;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import parser.SimpleCBaseVisitor;
import parser.SimpleCParser;

import java.util.*;

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

    private List<String> assertConditions = new ArrayList<>();

    @Override
    public String visitProgram(SimpleCParser.ProgramContext ctx) {
        StringBuilder code = new StringBuilder();
        assert (ctx.procedures.size() == 1);
        for (SimpleCParser.ProcedureDeclContext proc: ctx.procedures) {
            code.append(visit(proc) + EOL);
        }

        if (!assertConditions.isEmpty()) {
            String andExpr = "(and %s (tobool %s))";
            String andAssertions = String.format("(tobool %s)", assertConditions.get(0));
            for (int i = 1; i < assertConditions.size(); i++) {
                andAssertions = String.format(andExpr, andAssertions, assertConditions.get(i));
            }
            code.append(String.format("(assert (not %s))", andAssertions) + EOL);
        }


        return code.toString();
    }

    @Override
    public String visitProcedureDecl(SimpleCParser.ProcedureDeclContext ctx) {
        StringBuilder code = new StringBuilder();
        for (SimpleCParser.StmtContext stmt: ctx.stmt()) {
            code.append(visit(stmt) + EOL);
        }

        return code.toString();
    }

    @Override
    public String visitFormalParam(SimpleCParser.FormalParamContext ctx) {
        return super.visitFormalParam(ctx);
    }

    @Override
    public String visitPrepost(SimpleCParser.PrepostContext ctx) {
        return super.visitPrepost(ctx);
    }

    @Override
    public String visitRequires(SimpleCParser.RequiresContext ctx) {
        return super.visitRequires(ctx);
    }

    @Override
    public String visitEnsures(SimpleCParser.EnsuresContext ctx) {
        return super.visitEnsures(ctx);
    }

    @Override
    public String visitCandidateRequires(SimpleCParser.CandidateRequiresContext ctx) {
        return super.visitCandidateRequires(ctx);
    }

    @Override
    public String visitCandidateEnsures(SimpleCParser.CandidateEnsuresContext ctx) {
        return super.visitCandidateEnsures(ctx);
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
    public String visitAssumeStmt(SimpleCParser.AssumeStmtContext ctx) {
        return super.visitAssumeStmt(ctx);
    }

    @Override
    public String visitHavocStmt(SimpleCParser.HavocStmtContext ctx) {
        return super.visitHavocStmt(ctx);
    }

    @Override
    public String visitCallStmt(SimpleCParser.CallStmtContext ctx) {
        return super.visitCallStmt(ctx);
    }

    @Override
    public String visitIfStmt(SimpleCParser.IfStmtContext ctx) {
        return super.visitIfStmt(ctx);
    }

    @Override
    public String visitWhileStmt(SimpleCParser.WhileStmtContext ctx) {
        return super.visitWhileStmt(ctx);
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
    public String visitLoopInvariant(SimpleCParser.LoopInvariantContext ctx) {
        return super.visitLoopInvariant(ctx);
    }

    @Override
    public String visitInvariant(SimpleCParser.InvariantContext ctx) {
        return super.visitInvariant(ctx);
    }

    @Override
    public String visitCandidateInvariant(SimpleCParser.CandidateInvariantContext ctx) {
        return super.visitCandidateInvariant(ctx);
    }

    @Override
    public String visitExpr(SimpleCParser.ExprContext ctx) {
        return visit(ctx.ternExpr());
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

        String cond = "(ite (tobool %s) %s %s)";
        String code = childrenResults.get(0);
        for (int i = 1; i < childrenResults.size(); i += 2) {
            String currChild = childrenResults.get(i);
            String nextChild = childrenResults.get(i + 1);
            code = String.format(cond, code.toString(), currChild, nextChild);
        }

        return code;
    }

    @Override
    public String visitLorExpr(SimpleCParser.LorExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> childrenResults = new ArrayList<>();
        for (SimpleCParser.LandExprContext child: ctx.args) {
            childrenResults.add(visit(child));
        }

        // i.e. (firstTerm secondTerm)
        String orExpr = "(or %s (tobool %s))";
        String code = String.format("(tobool %s)", childrenResults.get(0));
        for (int i = 1; i < childrenResults.size(); i++) {
            code = String.format(orExpr, code, childrenResults.get(i));
        }

        return String.format("(tobv32 %s)", code);
    }

    @Override
    public String visitLandExpr(SimpleCParser.LandExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> childrenResults = new ArrayList<>();
        for (SimpleCParser.BorExprContext child: ctx.args) {
            childrenResults.add(visit(child));
        }

        // i.e. (firstTerm secondTerm)
        String andExpr = "(and %s (tobool %s))";
        String code = String.format("(tobool %s)", childrenResults.get(0));
        for (int i = 1; i < childrenResults.size(); i++) {
            code = String.format(andExpr, code, childrenResults.get(i));
        }

        return String.format("(tobv32 %s)", code);
    }

    @Override
    public String visitBorExpr(SimpleCParser.BorExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> childrenResults = new ArrayList<>();
        for (SimpleCParser.BxorExprContext child: ctx.args) {
            childrenResults.add(visit(child));
        }

        // i.e. (firstTerm secondTerm)
        String bitwiseOrExpr = "(bvor %s %s)";
        String code = childrenResults.get(0);
        for (int i = 1; i < childrenResults.size(); i++) {
            code = String.format(bitwiseOrExpr, code, childrenResults.get(i));
        }

        return code;
    }

    @Override
    public String visitBxorExpr(SimpleCParser.BxorExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> childrenResults = new ArrayList<>();
        for (SimpleCParser.BandExprContext child: ctx.args) {
            childrenResults.add(visit(child));
        }

        // i.e. (firstTerm secondTerm)
        String bitwiseXorExpr = "(bvxor %s %s)";
        String code = childrenResults.get(0);
        for (int i = 1; i < childrenResults.size(); i++) {
            code = String.format(bitwiseXorExpr, code, childrenResults.get(i));
        }

        return code;
    }

    @Override
    public String visitBandExpr(SimpleCParser.BandExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> childrenResults = new ArrayList<>();
        for (SimpleCParser.EqualityExprContext child: ctx.args) {
            childrenResults.add(visit(child));
        }

        // i.e. (firstTerm secondTerm)
        String bitwiseAndExpr = "(bvand %s %s)";
        String code = childrenResults.get(0);
        for (int i = 1; i < childrenResults.size(); i++) {
            code = String.format(bitwiseAndExpr, code, childrenResults.get(i));
        }

        return code;
    }

    @Override
    public String visitEqualityExpr(SimpleCParser.EqualityExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> childrenResults = new ArrayList<>();
        for (SimpleCParser.RelExprContext child: ctx.args) {
            childrenResults.add(visit(child));
        }

        Map<String, String> equalityOperatorToSSA = new HashMap<String, String>() {{
           put("==", "(tobv32 (= %s %s))");
           put("!=", "(tobv32 (not (= %s %s)))");
        }};

        Iterator<Token> currToken = ctx.ops.iterator();
        String code = childrenResults.get(0);
        for (int i = 1; i < childrenResults.size(); i++) {
            String equalityExpr = equalityOperatorToSSA.get(currToken.next().getText());
            code = String.format(equalityExpr, code, childrenResults.get(i));
        }

        return code;
    }

    @Override
    public String visitRelExpr(SimpleCParser.RelExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> childrenResults = new ArrayList<>();
        for (SimpleCParser.ShiftExprContext child: ctx.args) {
            childrenResults.add(visit(child));
        }

        Map<String, String> relOperatorToSSA = new HashMap<String, String>() {{
            put("<", "(tobv32 (bvslt %s %s))");
            put("<=", "(tobv32 (bvsle %s %s))");
            put(">", "(tobv32 (bvsgt %s %s))");
            put(">=", "(tobv32 (bvsge %s %s))");
        }};

        Iterator<Token> currToken = ctx.ops.iterator();
        String code = childrenResults.get(0);
        for (int i = 1; i < childrenResults.size(); i++) {
            String equalityExpr = relOperatorToSSA.get(currToken.next().getText());
            code = String.format(equalityExpr, code, childrenResults.get(i));
        }

        return code;
    }

    @Override
    public String visitShiftExpr(SimpleCParser.ShiftExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> childrenResults = new ArrayList<>();
        for (SimpleCParser.AddExprContext child: ctx.args) {
            childrenResults.add(visit(child));
        }

        Map<String, String> shiftOperatorToSSA = new HashMap<String, String>() {{
            put("<<", "(bvshl %s %s)");
            put(">>", "(bvashr %s %s)");
        }};

        Iterator<Token> currToken = ctx.ops.iterator();
        String code = childrenResults.get(0);
        for (int i = 1; i < childrenResults.size(); i++) {
            String equalityExpr = shiftOperatorToSSA.get(currToken.next().getText());
            code = String.format(equalityExpr, code, childrenResults.get(i));
        }

        return code;
    }

    @Override
    public String visitAddExpr(SimpleCParser.AddExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> childrenResults = new ArrayList<>();
        for (SimpleCParser.MulExprContext child: ctx.args) {
            childrenResults.add(visit(child));
        }

        Map<String, String> addSubOperatorToSSA = new HashMap<String, String>() {{
            put("+", "(bvadd %s %s)");
            put("-", "(bvsub %s %s)");
        }};

        Iterator<Token> currToken = ctx.ops.iterator();
        String code = childrenResults.get(0);
        for (int i = 1; i < childrenResults.size(); i++) {
            String equalityExpr = addSubOperatorToSSA.get(currToken.next().getText());
            code = String.format(equalityExpr, code, childrenResults.get(i));
        }

        return code;
    }

    @Override
    public String visitMulExpr(SimpleCParser.MulExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<String> childrenResults = new ArrayList<>();
        for (SimpleCParser.UnaryExprContext child: ctx.args) {
            childrenResults.add(visit(child));
        }

        Map<String, String> mulDivModOperatorToSSA = new HashMap<String, String>() {{
            put("*", "(bvmul %s %s)");
            put("/", "(bvdiv %s %s)");
            put("%", "(bvsmod %s %s)");
        }};

        Iterator<Token> currToken = ctx.ops.iterator();
        String code = childrenResults.get(0);
        for (int i = 1; i < childrenResults.size(); i++) {
            String equalityExpr = mulDivModOperatorToSSA.get(currToken.next().getText());
            code = String.format(equalityExpr, code, childrenResults.get(i));
        }

        return code;
    }

    @Override
    public String visitUnaryExpr(SimpleCParser.UnaryExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        Map<String, String> unaryOperatorToSSA = new HashMap<String, String>() {{
            put("+", "%s");
            put("-", "(bvneg %s)");
            put("!", "(tobv32 (not (tobool %s)))");
            put("~", "(bvnot %s)");
        }};

        String code = visit(ctx.arg);
        for (Token op: ctx.ops) {
            String unaryExpr = unaryOperatorToSSA.get(op.getText());
            code = String.format(unaryExpr, code);
        }

        return code;
    }

    @Override
    public String visitAtomExpr(SimpleCParser.AtomExprContext ctx) {
        // it does seem to have only one child
        return visit(ctx.getChild(0));
    }

    @Override
    public String visitNumberExpr(SimpleCParser.NumberExprContext ctx) {
        String noFormat = "(_ bv%s 32)";

        return String.format(noFormat, ctx.number.getText());
    }

    @Override
    public String visitVarrefExpr(SimpleCParser.VarrefExprContext ctx) {
        return visit(ctx.var);
    }

    @Override
    public String visitParenExpr(SimpleCParser.ParenExprContext ctx) {
        String childResult = visit(ctx.arg);

        return String.format("%s", childResult);
    }

    @Override
    public String visitResultExpr(SimpleCParser.ResultExprContext ctx) {
        return super.visitResultExpr(ctx);
    }

    @Override
    public String visitOldExpr(SimpleCParser.OldExprContext ctx) {
        return super.visitOldExpr(ctx);
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
