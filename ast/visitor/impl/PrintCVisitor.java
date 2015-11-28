package ast.visitor.impl;

import ast.*;
import tool.ScopesHandler;
import tool.VariableIdsGenerator;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

public class PrintCVisitor extends PrintVisitor {

    private static final String IF_NOT_RETURN = "if (!(%s)) return 0;\n";

    private static final String IF_STMT = "if (%s) \n";

    private static final String ELSE_STMT = "else\n";

    private static final String ASSERT_STMT = "assert (%s);\n";

    protected static final String WHILE_COND = "while (%s) { \n";

    private static final String SPEC_DIV = "mydiv(%s, %s)";

    private static final String SPEC_MOD = "mymod(%s, %s)";

    private static final String SPEC_ADD = "myadd(%s, %s)";

    private static final String SPEC_SUB = "mysub(%s, %s)";

    private static final String SPEC_MUL = "mymul(%s, %s)";

    private static final String SPEC_LEFT_SHIFT = "myleftshift(%s, %s)";

    private static final String SPEC_RIGHT_SHIFT = "myrightshift(%s, %s)";

    private static final String RAND_STMT = "srand(time(0));\n";

    private static final String GLOBAL_TEMP = "%scopy";

    private static final String VAR_DECL = "int %s = %s;\n";

    private List<String> globals;

    private Map<String, String> enclosingMethodGlobalsCopy;

    private ScopesHandler scopesHandler;

    private String methodName;

    private Map<Node, Integer> nodeValues;

    private Program program;

    public PrintCVisitor(Program program, String methodName, Map<Node, Integer> nodeValues) {
        this.program = program;
        this.methodName = methodName;
        this.nodeValues = nodeValues;

        scopesHandler = new ScopesHandler(new VariableIdsGenerator());

        globals = new LinkedList<>();
        for (VarDecl varDecl: program.getVarDecls()) {
            globals.add(varDecl.getVarIdentifier().getVarName());
        }
    }

    @Override
    public String visit(Program program) {
        StringBuilder sb = new StringBuilder();

        for (VarDecl varDecl: program.getVarDecls()) {
            sb.append(varDecl.accept(this));
        }

        for (ProcedureDecl procedureDecl: program.getProcedureDecls()) {
            if (procedureDecl.getMethodName().equals(methodName)) {
                sb.append(procedureDecl.accept(this));
            }
        }

        return sb.toString();
    }

    @Override
    public String visit(AssertStmt assertStmt) {
        return ident.getIndent() + String.format(ASSERT_STMT, assertStmt.getCondition().accept(this));
    }

    @Override
    public String visit(ProcedureDecl procedureDecl) {
        scopesHandler.pushMethodsStack(procedureDecl);
        StringBuilder sb = new StringBuilder();

        // method declaration
        sb.append(ident.getIndent() + String.format(METHOD_ANTET, procedureDecl.getMethodName(), ""));

        // begin method body
        sb.append(ident.getIndent() + "{" + EOL);
        ident.push();

        // add copies after global variables
        enclosingMethodGlobalsCopy = new HashMap<>();
        for (String global: globals) {
            String globalCopy = String.format(GLOBAL_TEMP, global);
            sb.append(ident.getIndent() + String.format(VAR_DECL, globalCopy, global));
            enclosingMethodGlobalsCopy.put(global, globalCopy);
        }

        // add formal parameters
        sb.append(ident.getIndent() + RAND_STMT);
        for (FormalParam formalParam: procedureDecl.getParamList()) {
            String varName = formalParam.getVarIdentifier().getVarName();
            sb.append(ident.getIndent() + String.format(VAR_DECL, varName, nodeValues.get(formalParam)));
        }

        // add preconditions as assumes
        for (PrePostCondition prePostCondition : procedureDecl.getPrePostConditions()) {
            if (prePostCondition instanceof Precondition) {
                sb.append(ident.getIndent() + String.format(IF_NOT_RETURN, prePostCondition.accept(this)));
            }
        }

        // add statements
        for (Stmt stmt: procedureDecl.getStmts()) {
            sb.append(stmt.accept(this));
        }

        // add postconditions as asserts
        for (PrePostCondition prePostCondition : procedureDecl.getPrePostConditions()) {
            if (prePostCondition instanceof Postcondition) {
                sb.append(ident.getIndent() + String.format(ASSERT_STMT, prePostCondition.accept(this)));
            }
        }

        // add return stmt
        sb.append(ident.getIndent() + String.format(RETURN_STMT, procedureDecl.getReturnExpr().accept(this)));

        ident.pop();
        sb.append(ident.getIndent() + "}" + EOL);

        scopesHandler.popMethodsStack();

        return sb.toString();
    }

    @Override
    public String visit(Precondition precondition) {
        return (String) precondition.getCondition().accept(this);
    }

    @Override
    public String visit(Postcondition postcondition) {
        return (String) postcondition.getCondition().accept(this);
    }

    @Override
    public String visit(HavocStmt havocStmt) {
        String varName = (String) havocStmt.getVar().accept(this);
        return ident.getIndent() + String.format("%s = %s;\n", varName, nodeValues.get(havocStmt));
    }

    @Override
    public String visit(VarDecl varDecl) {
        String varName = (String) varDecl.getVarIdentifier().accept(this);
        return ident.getIndent() + String.format(VAR_DECL, varName, nodeValues.get(varDecl));
    }

    @Override
    public String visit(AssumeStmt assumeStmt) {
        return ident.getIndent() + String.format(IF_NOT_RETURN, assumeStmt.getCondition().accept(this));
    }

    @Override
    public String visit(IfStmt ifStmt) {
        StringBuilder sb = new StringBuilder();

        // add if condition
        sb.append(ident.getIndent() + String.format(IF_STMT, ifStmt.getCondition().accept(this)));
        // then
        ident.push();
        sb.append(ifStmt.getThenBlock().accept(this));
        ident.pop();

        // else
        sb.append(ident.getIndent() + ELSE_STMT);
        ident.push();
        sb.append(ifStmt.getElseBlock().accept(this));
        ident.pop();

        sb.append(EOL);
        return sb.toString();
    }

    @Override
    public String visit(WhileStmt whileStmt) {
        StringBuilder sb = new StringBuilder();

        // assert invariants on entry
        for (LoopInvariant invariant: whileStmt.getLoopInvariantList()) {
            if (invariant instanceof Invariant) {
                Expr invExpr = ((Invariant) invariant).getCondition();
                sb.append(ident.getIndent() + String.format(ASSERT_STMT, invExpr.accept(this)));
            }
        }

        // while condition
        sb.append(ident.getIndent() + String.format(WHILE_COND, whileStmt.getCondition().accept(this)));
        // loop body
        ident.push();
        sb.append(whileStmt.getBody().accept(this));
        // invariants hold at each iteration
        for (LoopInvariant invariant: whileStmt.getLoopInvariantList()) {
            if (invariant instanceof Invariant) {
                Expr invExpr = ((Invariant) invariant).getCondition();
                sb.append(ident.getIndent() + String.format(ASSERT_STMT, invExpr.accept(this)));
            }
        }
        ident.pop();
        sb.append(ident.getIndent() + "}\n");

        return sb.toString();
    }

    @Override
    public String visit(BinaryExpr binaryExpr) {
        String lhs = (String) binaryExpr.getLhs().accept(this);
        String rhs = (String) binaryExpr.getRhs().accept(this);
        String op = binaryExpr.getBinaryOp();
        switch (op) {
            case "/":
                return String.format(SPEC_DIV, lhs, rhs);
            case "%":
                return String.format(SPEC_MOD, lhs, rhs);
            case "+":
                return String.format(SPEC_ADD, lhs, rhs);
            case "-":
                return String.format(SPEC_SUB, lhs, rhs);
            case "*":
                return String.format(SPEC_MUL, lhs, rhs);
            case "<<":
                return String.format(SPEC_LEFT_SHIFT, lhs, rhs);
            case ">>":
                return String.format(SPEC_RIGHT_SHIFT, lhs, rhs);
        }

        return super.visit(binaryExpr);
    }

    @Override
    public String visit(OldExpr oldExpr) {
        String varName = oldExpr.getVar().getVarIdentifier().getVarName();
        return enclosingMethodGlobalsCopy.get(varName);
    }

    @Override
    public String visit(ResultExpr resultExpr) {
        return (String) scopesHandler.getEnclosingMethod().getReturnExpr().accept(this);
    }
}
