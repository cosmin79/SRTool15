package ast;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import parser.SimpleCBaseVisitor;
import parser.SimpleCParser.*;

import java.util.*;

public class AntlrToAstConverter extends SimpleCBaseVisitor<Node> {

    @Override
    public Node visitProgram(ProgramContext ctx) {
        List<VarDecl> globals = new LinkedList<>();
        List<ProcedureDecl> procedures = new LinkedList<>();

        if (ctx.globals != null) {
            for (VarDeclContext varDecl : ctx.globals) {
                globals.add((VarDecl) visit(varDecl));
            }
        }

        if (ctx.procedures != null) {
            for (ProcedureDeclContext procDecl: ctx.procedures) {
                procedures.add((ProcedureDecl) visit(procDecl));
            }
        }

        return new Program(globals, procedures);
    }

    @Override
    public Node visitVarDecl(VarDeclContext ctx) {
        return new VarDecl((VarIdentifier) visit(ctx.ident));
    }

    @Override
    public Node visitProcedureDecl(ProcedureDeclContext ctx) {
        String methodName = ctx.name.getText();
        List<FormalParam> formalParams = new LinkedList<>();
        List<PrePostCondition> prePostConditions = new LinkedList<>();
        List<Stmt> stmts = new LinkedList<>();

        if (ctx.formals != null) {
            for (FormalParamContext param: ctx.formals) {
                formalParams.add((FormalParam) visit(param));
            }
        }

        if (ctx.contract != null) {
            for (PrepostContext prePostCondition: ctx.contract) {
                prePostConditions.add((PrePostCondition) visit(prePostCondition));
            }
        }

        for (StmtContext stmt: ctx.stmt()) {
            stmts.add((Stmt) visit(stmt));
        }

        Expr resultExpr = (Expr) visit(ctx.returnExpr);

        return new ProcedureDecl(methodName, formalParams, prePostConditions, stmts, resultExpr);
    }

    @Override
    public Node visitFormalParam(FormalParamContext ctx) {
        return new FormalParam((VarIdentifier) visit(ctx.ident));
    }

    @Override
    public Node visitRequires(RequiresContext ctx) {
        return new Precondition((Expr) visit(ctx.condition));
    }

    @Override
    public Node visitEnsures(EnsuresContext ctx) {
        return new Postcondition((Expr) visit(ctx.condition));
    }

    @Override
    public Node visitCandidateRequires(CandidateRequiresContext ctx) {
        return new CandidatePrecondition((Expr) visit(ctx.condition));
    }

    @Override
    public Node visitCandidateEnsures(CandidateEnsuresContext ctx) {
        return new CandidatePostcondition((Expr) visit(ctx.condition));
    }

    @Override
    public Node visitAssignStmt(AssignStmtContext ctx) {
        return new AssignStmt((VarRef) visit(ctx.lhs), (Expr) visit(ctx.rhs));
    }

    @Override
    public Node visitAssertStmt(AssertStmtContext ctx) {
        return new AssertStmt((Expr) visit(ctx.condition));
    }

    @Override
    public Node visitAssumeStmt(AssumeStmtContext ctx) {
        return new AssumeStmt((Expr) visit(ctx.condition));
    }

    @Override
    public Node visitHavocStmt(HavocStmtContext ctx) {
        return new HavocStmt((VarRef) visit(ctx.var));
    }

    @Override
    public Node visitCallStmt(CallStmtContext ctx) {
        VarRef lhsVar = (VarRef) visit(ctx.lhs);
        String methodName = ctx.callee.getText();

        List<Expr> parameters = new LinkedList<>();
        for (ExprContext expr: ctx.expr()) {
            parameters.add((Expr) visit(expr));
        }

        return new CallStmt(lhsVar, methodName, parameters);
    }

    @Override
    public Node visitIfStmt(IfStmtContext ctx) {
        Expr condition = (Expr) visit(ctx.condition);
        BlockStmt thenBlock = (BlockStmt) visit(ctx.thenBlock);
        // create an empty block if there is no else branch to have a canonic "if then else" node
        BlockStmt elseBlock = ctx.elseBlock != null ?
                (BlockStmt) visit(ctx.elseBlock) : new BlockStmt();

        return new IfStmt(condition, thenBlock, elseBlock);
    }

    @Override
    public Node visitWhileStmt(WhileStmtContext ctx) {
        Expr condition = (Expr) visit(ctx.condition);
        List<LoopInvariant> loopInvariants = new LinkedList<>();
        BlockStmt body = (BlockStmt) visit(ctx.body);

        if (ctx.invariantAnnotations != null) {
            for (LoopInvariantContext invariant: ctx.invariantAnnotations) {
                loopInvariants.add((LoopInvariant) visit(invariant));
            }
        }

        return new WhileStmt(condition, loopInvariants, body);
    }

    @Override
    public Node visitBlockStmt(BlockStmtContext ctx) {
        List<Stmt> stmts = new LinkedList<>();
        for (StmtContext stmt: ctx.stmts) {
            stmts.add((Stmt) visit(stmt));
        }

        return new BlockStmt(stmts);
    }

    @Override
    public Node visitInvariant(InvariantContext ctx) {
        return new Invariant((Expr) visit(ctx.condition));
    }

    @Override
    public Node visitCandidateInvariant(CandidateInvariantContext ctx) {
        return new CandidateInvariant((Expr) visit(ctx.condition));
    }

    @Override
    public Node visitTernExpr(TernExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        List<Expr> childrenExprs = new ArrayList<>();
        for (LorExprContext child: ctx.args) {
            childrenExprs.add((Expr) visit(child));
        }

        Collections.reverse(childrenExprs);
        Expr rhsChild = childrenExprs.get(0);
        for (int i = 1; i < childrenExprs.size(); i += 2) {
            Expr lhsChild = childrenExprs.get(i);
            Expr condChild = childrenExprs.get(i + 1);
            rhsChild = new TernExpr(condChild, lhsChild, rhsChild);
        }

        return rhsChild;
    }

    /**
     * Processes an expression's children ; the expected general form of the expression is:
     *
     * child_1 sep_1 child_2 sep_2 ... sep_(n - 1) child_n
     **/
    private<T extends ParserRuleContext> Node generateFromChildrenExpr(List<T> childrenCtx, List<Token> sep) {
        List<Expr> childrenResults = new ArrayList<>();
        for (T child: childrenCtx) {
            childrenResults.add((Expr) visit(child));
        }

        Expr result = childrenResults.get(0);
        Iterator<Token> currToken = sep.iterator();
        for (int i = 1; i < childrenResults.size(); i++) {
            Expr currChild = childrenResults.get(i);
            result = new BinaryExpr(currToken.next().getText(), result, currChild);
        }

        return result;
    }

    @Override
    public Node visitLorExpr(LorExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }
        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public Node visitLandExpr(LandExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }
        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public Node visitBorExpr(BorExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }
        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public Node visitBxorExpr(BxorExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }
        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public Node visitBandExpr(BandExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }
        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public Node visitEqualityExpr(EqualityExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }
        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public Node visitRelExpr(RelExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }
        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public Node visitShiftExpr(ShiftExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }
        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public Node visitAddExpr(AddExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }
        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public Node visitMulExpr(MulExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }
        return generateFromChildrenExpr(ctx.args, ctx.ops);
    }

    @Override
    public Node visitUnaryExpr(UnaryExprContext ctx) {
        if (ctx.single != null) {
            return visit(ctx.single);
        }

        Expr expr = (Expr) visit(ctx.arg);
        // apply the unary operators right to left
        Collections.reverse(ctx.ops);
        for (Token op: ctx.ops) {
            expr = new UnaryExpr(op.getText(), expr);
        }

        return expr;
    }

    @Override
    public Node visitNumberExpr(NumberExprContext ctx) {
        return new NumberExpr(Integer.parseInt(ctx.number.getText()));
    }

    @Override
    public Node visitVarrefExpr(VarrefExprContext ctx) {
        return new VarRefExpr((VarRef) visit(ctx.var));
    }

    @Override
    public Node visitParenExpr(ParenExprContext ctx) {
        return new ParenExpr((Expr) visit(ctx.arg));
    }

    @Override
    public Node visitResultExpr(ResultExprContext ctx) {
        return new ResultExpr();
    }

    @Override
    public Node visitOldExpr(OldExprContext ctx) {
        return new OldExpr((VarRef) visit(ctx.arg));
    }

    @Override
    public Node visitVarref(VarrefContext ctx) {
        return new VarRef((VarIdentifier) visit(ctx.ident));
    }

    @Override
    public Node visitVarIdentifier(VarIdentifierContext ctx) {
        return new VarIdentifier(ctx.name.getText());
    }
}
