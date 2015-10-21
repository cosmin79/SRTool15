package tool;


import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import parser.SimpleCBaseVisitor;
import parser.SimpleCParser;

import javax.xml.soap.Node;
import java.util.*;

class NodeResult {

    StringBuilder code;
    Set<String> modSet;
    // it's not quite sure what this is supposed to represent..
    // ideally it should be the mappings from modSet to actual integer
    Map<String, Integer> modifiedMapping;

    public NodeResult() {
        code = new StringBuilder();
        modSet = new HashSet<>();
        modifiedMapping = new HashMap<>();
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
};

public class SimpleCToSSA extends SimpleCBaseVisitor<NodeResult> {

    private static final String EOL = "\n";

    private static final String ASSIGN_STMT = "%s=%s;\n";

    private static final String ASSERT_STMT = "assert %s;\n";

    private static final String PROGRAM = "int main() {\n%s\nreturn 0;\n}\n";

    private List<Map<String, Integer>> varStack = new LinkedList<>();

    private List<Set<String>> modSetStack = new LinkedList<>();

    private Map<String, Integer> freshIds = new HashMap<>();

    public SimpleCToSSA(Map<String, Integer> globals) {
        varStack.add(0, globals);
        for (String var: globals.keySet()) {
            freshIds.put(var, 0);
        }
    }

    // HELPER methods start
    Integer generateFresh(String name) {
        Integer prevUse = freshIds.get(name);
        Integer newId = prevUse == null ? 0 : prevUse + 1;
        freshIds.put(name, newId);

        return newId;
    }

    private Map<String, Integer> peekLocalsStack() {
        return varStack.get(0);
    }

    private Map<String, Integer> popLocalsStack() {
        return varStack.remove(0);
    }

    private void pushLocalsStack() {
        varStack.add(0, new HashMap<>());
    }

    void addVariableToScope(String name) {
        Integer newId = generateFresh(name);
        peekLocalsStack().put(name, newId);
    }

    String latestVarRef(String name) {
        return String.format("%s%d", name, peekLocalsStack().get(name));
    }
    // HELPER methods end

    @Override
    public NodeResult visitProcedureDecl(SimpleCParser.ProcedureDeclContext ctx) {
        StringBuilder code = new StringBuilder();
        Set<String> modSet = new HashSet<>();

        pushLocalsStack();
        for (SimpleCParser.StmtContext stmt: ctx.stmt()) {
            NodeResult stmtResult = visit(stmt);

            code.append(stmtResult.getCode() + EOL);
            modSet.addAll(stmtResult.getModSet());
        }
        popLocalsStack();

        String resultCode = String.format(PROGRAM, code);
        return new NodeResult(new StringBuilder(resultCode), modSet);
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

        // create new variable entry
        String name = ctx.lhs.ident.name.getText();
        addVariableToScope(name);

        // add statement of assignment
        NodeResult rhsResult = visit(ctx.rhs);
        code.append(String.format(ASSIGN_STMT, latestVarRef(name), rhsResult.getCode()));

        // update modSet
        modSet.addAll(rhsResult.modSet);
        modSet.add(name);

        return new NodeResult(code, modSet);
    }

    @Override
    public NodeResult visitAssertStmt(SimpleCParser.AssertStmtContext ctx) {
        StringBuilder code = new StringBuilder();
        // obtain result of the underlying expression
        NodeResult condExpr = visit(ctx.condition);

        code.append(String.format(ASSERT_STMT, condExpr.getCode()));
        return new NodeResult(code, condExpr.getModSet());
    }

    @Override
    public NodeResult visitBlockStmt(SimpleCParser.BlockStmtContext ctx) {
        StringBuilder code = new StringBuilder();
        Set<String> modSet = new HashSet<>();

        pushLocalsStack();
        for (SimpleCParser.StmtContext stmt: ctx.stmts) {
            NodeResult stmtResult = visit(stmt);
            if (stmtResult != null) {
                code.append(stmtResult.getCode() + EOL);
                modSet.addAll(stmtResult.getModSet());
            }
        }
        popLocalsStack();

        return new NodeResult(code, modSet);
    }

    @Override
    public NodeResult visitVarIdentifier(SimpleCParser.VarIdentifierContext ctx) {
        StringBuilder code = new StringBuilder();
        Set<String> modSet = new HashSet<>();

        String name = ctx.getText();
        code.append(latestVarRef(name));
        modSet.add(name);

        return new NodeResult(code, modSet);
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

        return new NodeResult(code, modSet);
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

        return new NodeResult(code, modSet);
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

        return new NodeResult(code, modSet);
    }

    @Override
    public NodeResult visitAtomExpr(SimpleCParser.AtomExprContext ctx) {
        // it does seem to have only one child
        return visit(ctx.getChild(0));
    }

    @Override
    public NodeResult visitNumberExpr(SimpleCParser.NumberExprContext ctx) {
        return new NodeResult(new StringBuilder(ctx.number.getText()), new HashSet<>());
    }

    @Override
    public NodeResult visitVarrefExpr(SimpleCParser.VarrefExprContext ctx) {
        return visit(ctx.var);
    }

    @Override
    public NodeResult visitParenExpr(SimpleCParser.ParenExprContext ctx) {
        NodeResult child = visit(ctx.arg);
        String newCode = String.format("(%s)", child.getCode());

        return new NodeResult(new StringBuilder(newCode), new HashSet<>(child.getModSet()));
    }

    @Override
    public NodeResult visitResultExpr(SimpleCParser.ResultExprContext ctx) {
        return null;
    }

    @Override
    public NodeResult visitOldExpr(SimpleCParser.OldExprContext ctx) {
        return null;
    }
}
