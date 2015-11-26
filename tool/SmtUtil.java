package tool;

import ast.AssertStmt;
import ast.Node;

import java.util.*;

enum ArgType {
    INT,
    BOOLEAN;
}

enum BinaryOperator {
    OR(ArgType.BOOLEAN, ArgType.BOOLEAN, "(or %s %s)"),
    AND(ArgType.BOOLEAN, ArgType.BOOLEAN, "(and %s %s)"),

    BOR(ArgType.INT, ArgType.INT, "(bvor %s %s)"),
    BXOR(ArgType.INT, ArgType.INT, "(bvxor %s %s)"),
    BAND(ArgType.INT, ArgType.INT, "(bvand %s %s)"),

    EQ(ArgType.INT, ArgType.BOOLEAN, "(= %s %s)"),
    NEQ(ArgType.INT, ArgType.BOOLEAN, "(not (= %s %s))"),

    LT(ArgType.INT, ArgType.BOOLEAN, "(bvslt %s %s)"),
    LTE(ArgType.INT, ArgType.BOOLEAN, "(bvsle %s %s)"),
    GT(ArgType.INT, ArgType.BOOLEAN, "(bvsgt %s %s)"),
    GTE(ArgType.INT, ArgType.BOOLEAN, "(bvsge %s %s)"),

    LSHIFT(ArgType.INT, ArgType.INT, "(bvshl %s %s)"),
    RHIFT(ArgType.INT, ArgType.INT, "(bvashr %s %s)"),

    ADD(ArgType.INT, ArgType.INT, "(bvadd %s %s)"),
    SUB(ArgType.INT, ArgType.INT, "(bvsub %s %s)"),

    MUL(ArgType.INT, ArgType.INT, "(bvmul %s %s)"),
    DIV(ArgType.INT, ArgType.INT, "(bvdiv %s %s)"),
    MOD(ArgType.INT, ArgType.INT, "(bvsrem %s %s)");

    ArgType argType;
    ArgType retType;
    String smtExpression;

    BinaryOperator(ArgType argType, ArgType retType, String smtExpression) {
        this.argType = argType;
        this.retType = retType;
        this.smtExpression = smtExpression;
    }

    public ArgType getArgType() {
        return argType;
    }

    public ArgType getRetType() {
        return retType;
    }

    public String getSmtExpression() {
        return smtExpression;
    }
}

enum UnaryOperator {
    UPLUS("%s"),
    UMINUS("(bvneg %s)"),
    BOOL_NOT(String.format(SmtUtil.TO_INT_EXPR, String.format("(not %s)", SmtUtil.TO_BOOL_EXPR))),
    BINARY_NOT("(bvnot %s)");

    String smtExpression;

    UnaryOperator(String smtExpression) {
        this.smtExpression = smtExpression;
    }

    public String getSmtExpression() {
        return smtExpression;
    }
}

public class SmtUtil {
    public static final String TO_BOOL_EXPR = "(tobool %s)";

    public static final String TO_INT_EXPR = "(tobv32 %s)";

    private static final String TERN_EXPR = "(ite (tobool %s) %s %s)";

    private static final Map<String, BinaryOperator> binaryOperatorsMap = new HashMap<String, BinaryOperator>() {{
        put("||",  BinaryOperator.OR);
        put("&&", BinaryOperator.AND);
        put("|", BinaryOperator.BOR);
        put("^", BinaryOperator.BXOR);
        put("&", BinaryOperator.BAND);
        put("==", BinaryOperator.EQ);
        put("!=", BinaryOperator.NEQ);
        put("<", BinaryOperator.LT);
        put("<=", BinaryOperator.LTE);
        put(">", BinaryOperator.GT);
        put(">=", BinaryOperator.GTE);
        put("<<", BinaryOperator.LSHIFT);
        put(">>", BinaryOperator.RHIFT);
        put("+", BinaryOperator.ADD);
        put("-", BinaryOperator.SUB);
        put("*", BinaryOperator.MUL);
        put("/", BinaryOperator.DIV);
        put("%", BinaryOperator.MOD);
    }};

    private static final Map<String, UnaryOperator> unaryOperatorsMap = new HashMap<String, UnaryOperator>() {{
        put("+", UnaryOperator.UPLUS);
        put("-", UnaryOperator.UMINUS);
        put("!", UnaryOperator.BOOL_NOT);
        put("~", UnaryOperator.BINARY_NOT);
    }};

    private static String castFromTo(String expr, ArgType from, ArgType to) {
        if (from == to) {
            return expr;
        } else if (to == ArgType.BOOLEAN) {
            return String.format(TO_BOOL_EXPR, expr);
        }

        return String.format(TO_INT_EXPR, expr);
    }

    public static String applyBinary(String op, String arg1, String arg2) {
        BinaryOperator operator = binaryOperatorsMap.get(op);
        arg1 = castFromTo(arg1, ArgType.INT, operator.getArgType());
        arg2 = castFromTo(arg2, ArgType.INT, operator.getArgType());

        String res = String.format(operator.getSmtExpression(), arg1, arg2);
        return castFromTo(res, operator.getRetType(), ArgType.INT);
    }

    public static String applyUnary(String op, String arg) {
        UnaryOperator operator = unaryOperatorsMap.get(op);
        String result = String.format(operator.getSmtExpression(), arg);

        return result;
    }

    public static String applyTern(String cond, String arg1, String arg2) {
        return String.format(TERN_EXPR, cond, arg1, arg2);
    }

    public static Set<Node> getAllFailedNodes(Map<Node, Node> predMap, SMTResult smtResult) {
        Set<Node> result = new HashSet<>();
        Iterator<AssertStmt> assertStmtIterator = smtResult.getFailedAsserts().iterator();
        while (assertStmtIterator.hasNext()) {
            Node stmt = assertStmtIterator.next();
            while (stmt != null) {
                result.add(stmt);
                stmt = predMap.get(stmt);
            }
        }

        return result;
    }

    public static Map<Node, Integer> getNodeValues(Map<Node, Node> predMap, SMTResult smtResult) {
        Map<Node, Integer> nodeValues = new HashMap<>();
        Iterator<Map.Entry<Node, Integer>> varValuesIterator = smtResult.getVarNodeToValue().entrySet().iterator();
        while (varValuesIterator.hasNext()) {
            Map.Entry<Node, Integer> currVariable = varValuesIterator.next();
            Node varNode = currVariable.getKey();
            while (varNode != null) {
                nodeValues.put(varNode, currVariable.getValue());
                varNode = predMap.get(varNode);
            }
        }

        return nodeValues;
    }
}
