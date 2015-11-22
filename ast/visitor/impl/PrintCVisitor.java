package ast.visitor.impl;

import ast.*;

public class PrintCVisitor extends PrintVisitor {

    private static final String VAR_DECL = "int %s = rand();\n";

    private static final String HAVOC_VAR = "%s = rand();\n";

    private static final String IF_NOT_RETURN = "if (!(%s)) return 0;\n";

    private static final String IF_STMT = "if (%s) \n";

    private static final String ELSE_STMT = "else\n";

    private static final String ASSERT_STMT = "assert (%s);\n";

    private static final String SPEC_DIV = "mydiv(%s, %s)";

    private static final String LEFT_SHIFT = "myleftshift(%s, %s)";

    private Program program;

    public PrintCVisitor(Program program) {
        this.program = program;
    }

    @Override
    public String visit(AssertStmt assertStmt) {
        return ident.getIndent() + String.format(ASSERT_STMT, assertStmt.getCondition().accept(this));
    }

    @Override
    public String visit(ProcedureDecl procedureDecl) {
        StringBuilder sb = new StringBuilder();

        // method declaration
        sb.append(ident.getIndent() + String.format(METHOD_ANTET, procedureDecl.getMethodName(), ""));

        // begin method body
        sb.append(ident.getIndent() + "{" + EOL);
        ident.push();
        for (FormalParam formalParam: procedureDecl.getParamList()) {
            sb.append(ident.getIndent() + String.format(VAR_DECL, formalParam.getVarIdentifier().getVarName()));
        }

        // add statements
        for (Stmt stmt: procedureDecl.getStmts()) {
            sb.append(stmt.accept(this));
        }

        // add return stmt
        sb.append(ident.getIndent() + String.format(RETURN_STMT, procedureDecl.getReturnExpr().accept(this)));

        ident.pop();
        sb.append(ident.getIndent() + "}" + EOL);

        return sb.toString();
    }

    @Override
    public String visit(HavocStmt havocStmt) {
        return ident.getIndent() + String.format(HAVOC_VAR, havocStmt.getVar().accept(this));
    }

    @Override
    public String visit(VarDecl varDecl) {
        StringBuilder sb = new StringBuilder();
        sb.append(ident.getIndent() + String.format(VAR_DECL, varDecl.getVarIdentifier().accept(this)));

        return sb.toString();
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
    public String visit(BinaryExpr binaryExpr) {
        String lhs = (String) binaryExpr.getLhs().accept(this);
        String rhs = (String) binaryExpr.getRhs().accept(this);
        if (binaryExpr.getBinaryOp().equals("/")) {
            return String.format(SPEC_DIV, lhs, rhs);
        } else if (binaryExpr.getBinaryOp().equals("<<")) {
            return String.format(LEFT_SHIFT, lhs, rhs);
        }
        return super.visit(binaryExpr);
    }
}
