package ast.visitor.impl;

import ast.*;
import ast.visitor.Visitor;
import util.Indent;

import java.util.List;

public class PrintVisitor implements Visitor<String> {

    protected static final String EOL = "\n";

    protected static final String COMMA = ",";

    protected static final String SPACE = " ";

    protected static final String FORMAL_PARAM = "int %s";

    protected static final String VAR_DECL = "int %s;\n";

    protected static final String ASSIGN_STMT = "%s = %s;\n";

    protected static final String ASSERT_STMT = "assert %s;\n";

    protected static final String ASSUME_STMT = "assume %s;\n";

    protected static final String HAVOC_STMT = "havoc %s;\n";

    protected static final String IF_STMT = "if (%s) then:\n";

    protected static final String ELSE_STMT = "else:\n";

    protected static final String WHILE_COND = "while (%s)\n";

    protected static final String METHOD_ANTET = "int %s(%s)\n";

    protected static final String POSTCONDITION = "postcondition: %s";

    protected static final String CANDIDATE_POSTCONDITION = "candidate postcondition: %s";

    protected static final String PRECONDITION = "precondition: %s";

    protected static final String CANDIDATE_PRECONDITION = "candidate precondition: %s";

    protected static final String INVARIANT = "invariant: %s";

    protected static final String CANDIDATE_INVARIANT = "candidate invariant: %s";

    protected static final String CALL_STMT = "%s = %s(%s);\n";

    protected static final String PAREN_EXPR = "(%s)";

    protected static final String RESULT_EXPR = "\\result";

    protected static final String OLD_EXPR = "\\old(%s)";

    protected static final String TERN_EXPR = "%s ? %s : %s";

    protected static final String BINARY_EXPR = "(%s %s %s)";

    protected static final String UNARY_EXPR = "(%s %s)";

    protected static final String RETURN_STMT = "return %s;\n";

    protected final Indent ident = new Indent("\t");

    @Override
    public String visit(Program program) {
        StringBuilder sb = new StringBuilder();

        for (VarDecl varDecl: program.getVarDecls()) {
            sb.append(varDecl.accept(this));
        }

        for (ProcedureDecl procedureDecl: program.getProcedureDecls()) {
            sb.append(procedureDecl.accept(this));
        }

        return sb.toString();
    }

    @Override
    public String visit(VarDecl varDecl) {
        return ident.getIndent() + String.format(VAR_DECL, varDecl.getVarIdentifier().accept(this));
    }

    protected<T extends Node> String tokenSeparated(List<T> listNodes, String sep) {
        StringBuilder code = new StringBuilder();
        if (!listNodes.isEmpty()) {
            code.append(listNodes.get(0).accept(this));
            for (int idx = 1; idx < listNodes.size(); idx++) {
                code.append(sep + listNodes.get(idx).accept(this));
            }
        }

        return code.toString();
    }

    @Override
    public String visit(ProcedureDecl procedureDecl) {
        StringBuilder sb = new StringBuilder();

        // method declaration
        String parameters = tokenSeparated(procedureDecl.getParamList(), COMMA + SPACE);
        sb.append(ident.getIndent() + String.format(METHOD_ANTET, procedureDecl.getMethodName(), parameters));

        // pre-post conditions
        ident.push();
        String prePostConditions = tokenSeparated(procedureDecl.getPrePostConditions(), COMMA + EOL + ident.getIndent());
        sb.append(ident.getIndent() + prePostConditions + EOL);
        ident.pop();

        // begin method body
        sb.append(ident.getIndent() + "{" + EOL);
        ident.push();

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
    public String visit(FormalParam formalParam) {
        return String.format(FORMAL_PARAM, formalParam.getVarIdentifier().accept(this));
    }

    @Override
    public String visit(Precondition precondition) {
        return String.format(PRECONDITION, precondition.getCondition().accept(this));
    }

    @Override
    public String visit(Postcondition postcondition) {
        return String.format(POSTCONDITION, postcondition.getCondition().accept(this));
    }

    @Override
    public String visit(CandidatePrecondition candidatePrecondition) {
        return String.format(CANDIDATE_PRECONDITION, candidatePrecondition.getCondition().accept(this));
    }

    @Override
    public String visit(CandidatePostcondition candidatePostcondition) {
        return String.format(CANDIDATE_POSTCONDITION, candidatePostcondition.getCondition().accept(this));
    }

    @Override
    public String visit(AssignStmt assignStmt) {
        return ident.getIndent() + String.format(ASSIGN_STMT,
                assignStmt.getLhsVar().accept(this),
                assignStmt.getRhsExpr().accept(this));
    }

    @Override
    public String visit(AssertStmt assertStmt) {
        return ident.getIndent() + String.format(ASSERT_STMT, assertStmt.getCondition().accept(this));
    }

    @Override
    public String visit(AssumeStmt assumeStmt) {
        return ident.getIndent() + String.format(ASSUME_STMT, assumeStmt.getCondition().accept(this));
    }

    @Override
    public String visit(HavocStmt havocStmt) {
        return ident.getIndent() + String.format(HAVOC_STMT, havocStmt.getVar().accept(this));
    }

    @Override
    public String visit(CallStmt callStmt) {
        return ident.getIndent() + String.format(CALL_STMT, callStmt.getLhsVar().accept(this), callStmt.getMethodName(),
                tokenSeparated(callStmt.getParametersList(), COMMA + SPACE));
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

        // while condition
        sb.append(ident.getIndent() + String.format(WHILE_COND, whileStmt.getCondition().accept(this)));

        // invariants
        ident.push();
        String invariants = tokenSeparated(whileStmt.getLoopInvariantList(), COMMA + EOL + ident.getIndent());
        sb.append(ident.getIndent() + invariants);
        ident.pop();

        // loop body
        ident.push();
        sb.append(whileStmt.getBody().accept(this));
        ident.pop();

        return sb.toString();
    }

    @Override
    public String visit(BlockStmt blockStmt) {
        StringBuilder sb = new StringBuilder();
        sb.append(ident.getIndent() + "{\n");

        ident.push();
        for (Stmt stmt: blockStmt.getStmts()) {
            sb.append(stmt.accept(this));
        }
        ident.pop();

        sb.append(ident.getIndent() + "}\n");

        return sb.toString();
    }

    @Override
    public String visit(Invariant invariant) {
        return String.format(INVARIANT, invariant.getCondition().accept(this));
    }

    @Override
    public String visit(CandidateInvariant candidateInvariant) {
        return String.format(CANDIDATE_INVARIANT, candidateInvariant.getCondition().accept(this));
    }

    @Override
    public String visit(TernExpr ternExpr) {
        return String.format(TERN_EXPR,
                ternExpr.getCondition().accept(this),
                ternExpr.getThenExpr().accept(this),
                ternExpr.getElseExpr().accept(this));
    }

    @Override
    public String visit(BinaryExpr binaryExpr) {
        return String.format(BINARY_EXPR,
                binaryExpr.getLhs().accept(this),
                binaryExpr.getBinaryOp(),
                binaryExpr.getRhs().accept(this));
    }

    @Override
    public String visit(UnaryExpr unaryExpr) {
        return String.format(UNARY_EXPR, unaryExpr.getUnaryOp(), unaryExpr.getArg().accept(this));
    }

    @Override
    public String visit(NumberExpr numberExpr) {
        return numberExpr.getNumber().toString();
    }

    @Override
    public String visit(VarRefExpr varRefExpr) {
        return (String) varRefExpr.getVarRef().accept(this);
    }

    @Override
    public String visit(ParenExpr parenExpr) {
        return String.format(PAREN_EXPR, parenExpr.getExpr().accept(this));
    }

    @Override
    public String visit(ResultExpr resultExpr) {
        return RESULT_EXPR;
    }

    @Override
    public String visit(OldExpr oldExpr) {
        return String.format(OLD_EXPR, oldExpr.getVar().accept(this));
    }

    @Override
    public String visit(VarRef varRef) {
        return (String) varRef.getVarIdentifier().accept(this);
    }

    @Override
    public String visit(VarIdentifier varIdentifier) {
        return varIdentifier.getVarName();
    }
}
