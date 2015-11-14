package ast.visitor;

import ast.*;

public interface Visitor<T> {
    T visit(Program program);
    T visit(VarDecl varDecl);
    T visit(ProcedureDecl procedureDecl);
    T visit(FormalParam formalParam);
    T visit(Precondition precondition);
    T visit(Postcondition postcondition);
    T visit(CandidatePrecondition candidatePrecondition);
    T visit(CandidatePostcondition candidatePostcondition);
    T visit(AssignStmt assignStmt);
    T visit(AssertStmt assertStmt);
    T visit(AssumeStmt assumeStmt);
    T visit(HavocStmt havocStmt);
    T visit(CallStmt callStmt);
    T visit(IfStmt ifStmt);
    T visit(WhileStmt whileStmt);
    T visit(BlockStmt blockStmt);
    T visit(Invariant invariant);
    T visit(CandidateInvariant candidateInvariant);
    T visit(TernExpr ternExpr);
    T visit(BinaryExpr binaryExpr);
    T visit(UnaryExpr unaryExpr);
    T visit(NumberExpr numberExpr);
    T visit(VarRefExpr varRefExpr);
    T visit(ParenExpr parenExpr);
    T visit(ResultExpr resultExpr);
    T visit(OldExpr oldExpr);
    T visit(VarRef varRef);
    T visit(VarIdentifier varIdentifier);
}
