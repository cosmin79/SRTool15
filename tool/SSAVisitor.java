package tool;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;

import parser.SimpleCBaseVisitor;
import parser.SimpleCParser;
import java.lang.String;
import java.util.Iterator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;

public class SSAVisitor extends SimpleCBaseVisitor<SSAResult> {

  private boolean       shouldModify;
  private Scopes        scopes;
  private String        returnVariable;
  private Stack<String> guard;
  private Indent        indent;

  public SSAVisitor(List<String> globalVaribles) {
    shouldModify   = false;
    returnVariable = "returnVar";
    scopes         = new Scopes();
    guard          = new Stack<String>();
    indent         = new Indent("  ");
    /* Global scope. */
    beginScope(ScopeType.NORMAL, "");
    for (String variable : globalVaribles) {
      scopes.declareVariable(variable);
    }
  }

  private void beginScope(ScopeType type, String newGuard) {
    scopes.beginScope(type);
    indent.push();
    if (guard.empty() || guard.peek().length() == 0) {
      if (newGuard.length() == 0) {
        guard.push("");
      } else {
        guard.push("(" + newGuard + ")");
      }
    } else {
      if (newGuard.length() == 0) {
        guard.push(guard.peek());
      } else {
        guard.push(guard.peek() + " && (" + newGuard + ")");
      }
    }
  }

  private Map<String, Integer> endScope() {
    Map<String, Integer> map = scopes.endScope();
    guard.pop();
    indent.pop();
    return map;
  }

  /* Returns the declaration of all the variables used in the program. */
  private StringBuilder getDeclarations() {
    StringBuilder result = new StringBuilder();
    Iterator<Map.Entry<String, Integer>> it =
      scopes.getVariableDeclarations().entrySet().iterator();
    while (it.hasNext()) {
      Map.Entry<String, Integer> entry = it.next();
      for (int k = 0; k <= entry.getValue(); k++) {
        result.append("int ").append(entry.getKey()).append(k).append(";\n");
      }
    }
    return result;
  }

  /* Visit a list of statements and return them transformed to SSA form. */
  private SSAResult visitStatements(List<SimpleCParser.StmtContext> stmts) {
    SSAResult result = new SSAResult();
    for (SimpleCParser.StmtContext statement : stmts) {
      SSAResult res = visit(statement);
      StringBuilder code = res.getCode();
      if (code.length() > 0) {
        result.appendCode(indent.getIndent());
        result.appendCode(code);
        result.appendCode("\n");
      }
    }
    return result;
  }

  private enum Prepost {
    REQUIRES,
    ENSURES,
    CANDIDATE_REQUIRES,
    CANDIDATE_ENSURES
  }

  /* Process prepost conditions. */
  private SSAResult transformPrepost(
      List<SimpleCParser.PrepostContext> contract,
      Prepost prepost) {
    SSAResult result = new SSAResult();
    for (SimpleCParser.PrepostContext ctx : contract) {
      SSAResult condition = null;
      switch (prepost) {
        case REQUIRES:
          if (ctx.requires() != null) {
            condition = visit(ctx.requires());
          }
          break;
        case ENSURES:
          if (ctx.ensures() != null) {
            condition = visit(ctx.ensures());
          }
          break;
        case CANDIDATE_REQUIRES:
          if (ctx.candidateRequires() != null) {
            condition = visit(ctx.candidateRequires());
          }
          break;
        case CANDIDATE_ENSURES:
          if (ctx.candidateEnsures() != null) {
            condition = visit(ctx.candidateEnsures());
          }
          break;
      }
      if (condition != null) {
        result.appendCode(indent.getIndent());
        result.appendCode(condition.getCode());
        result.appendCode("\n");
      }
    }
    return result;
  }

  /* Declare variable called returnVar to hold the return value of function. */
  public SSAResult declareReturnVariable(SSAResult statement) {
    SSAResult result = new SSAResult();
    int index = scopes.updateVariable(returnVariable);
    result.appendCode(returnVariable + index);
    result.appendCode(" = ");
    result.appendCode(statement.getCode());
    result.appendCode(";");
    return result;
  }

  /* Visit expresion with binary operators. */
  private SSAResult visitBinaryExpression(
      List<? extends ParserRuleContext> terms,
      List<Token> operators) {
    Iterator<? extends ParserRuleContext> termIt = terms.iterator();
    Iterator<Token> operatorIt = operators.iterator();
    SSAResult result = visit(termIt.next());
    while (termIt.hasNext()) {
      SSAResult term = visit(termIt.next());
      String op = operatorIt.next().getText();
      result.appendCode(" ");
      result.appendCode(op);
      result.appendCode(" ");
      result.appendCode(term.getCode());
    }
    return result;
  }

  private void declareFunctionParams(
      List<SimpleCParser.FormalParamContext> params) {
    for (SimpleCParser.FormalParamContext param : params) {
      scopes.declareVariable(param.ident.name.getText());
    }
  }

  @Override
  public SSAResult visitVarDecl(SimpleCParser.VarDeclContext ctx) {
    String varName = ctx.ident.name.getText();
    scopes.declareVariable(varName);
    return new SSAResult();
  }

  @Override
  public SSAResult visitProcedureDecl(SimpleCParser.ProcedureDeclContext ctx) {
    /* declare function params
     * requires
     * program ensures
     */
    SSAResult result;
    SSAResult requires;
    SSAResult program;
    SSAResult returnStatement;
    SSAResult ensures;

    beginScope(ScopeType.NORMAL, "");
    declareFunctionParams(ctx.formals);

    result   = new SSAResult();
    requires = transformPrepost(ctx.contract, Prepost.REQUIRES);
    program  = visitStatements(ctx.stmts);
    returnStatement = declareReturnVariable(visit(ctx.returnExpr));
    ensures  = transformPrepost(ctx.contract, Prepost.ENSURES);

    StringBuilder declarations = getDeclarations();
    /* Declare everything globaly. */
    result.appendCode(declarations);
    /* Start the main method of the program. */
    result.appendCode("int main() {\n");

    /* Put all the requires as assumptions. */
    result.appendCode(indent.getIndent());
    result.appendCode("// Requires statements:\n");
    result.appendCode(requires.getCode());
    result.appendCode(indent.getIndent());
    result.appendCode("// Requires finished!\n");

    /* Put the code of the program. */
    result.appendCode(indent.getIndent());
    result.appendCode("// Program body:\n");
    result.appendCode(program.getCode());

    /* Put the return of the function in a variable. */
    result.appendCode(indent.getIndent());
    result.appendCode(returnStatement.getCode());
    result.appendCode("\n");

    /* Put all the ensures as asserts by replacing \result with the variable
     * that contains the return of the function. */
    result.appendCode(indent.getIndent());
    result.appendCode("// Ensures statements:\n");
    result.appendCode(ensures.getCode());
    result.appendCode(indent.getIndent());
    result.appendCode("// Ensures finished!\n");

    /* Return statement. */
    result.appendCode(indent.getIndent());
    result.appendCode("return ");
    result.appendCode(returnVariable + scopes.getCurrentIndex(returnVariable));
    result.appendCode(";\n");
    result.appendCode("}\n");
    result.changeVariables(endScope().keySet());
    System.out.println(result.getModifiedSet());
    return result;
  }

  @Override
  public SSAResult visitFormalParam(SimpleCParser.FormalParamContext ctx) {
    shouldModify = true;
    visitChildren(ctx);
    shouldModify = false;
    return new SSAResult();
  }

  @Override
  public SSAResult visitRequires(SimpleCParser.RequiresContext ctx) {
    SSAResult result = new SSAResult();
    result.appendCode("assume ");
    SSAResult expr = visit(ctx.condition);
    result.appendCode(expr.getCode());
    result.appendCode(";");
    return result;
  }

  @Override
  public SSAResult visitEnsures(SimpleCParser.EnsuresContext ctx) {
    SSAResult result = new SSAResult();
    SSAResult expr = visit(ctx.condition);
    result.appendCode("assert ");
    result.appendCode(expr.getCode());
    result.appendCode(";");
    return result;
  }

  @Override
  public SSAResult visitCandidateRequires(
      SimpleCParser.CandidateRequiresContext ctx) {
    SSAResult result = new SSAResult();
    result.appendCode("candidate_requires ");
    SSAResult expr = visit(ctx.condition);
    result.appendCode(expr.getCode());
    return result;
  }

  @Override
  public SSAResult visitCandidateEnsures(
      SimpleCParser.CandidateEnsuresContext ctx) {
    SSAResult result = new SSAResult();
    result.appendCode("candidate_ensures ");
    SSAResult expr = visit(ctx.condition);
    result.appendCode(expr.getCode());
    return result;
  }

  @Override
  public SSAResult visitAssignStmt(SimpleCParser.AssignStmtContext ctx) {
    SSAResult rhs = visit(ctx.rhs);
    shouldModify = true;
    SSAResult lhs = visit(ctx.lhs);
    shouldModify = false;

    SSAResult result = new SSAResult();
    result.appendCode(lhs.getCode());
    result.appendCode(" = ");
    result.appendCode(rhs.getCode());
    result.appendCode(";");
    return result;
  }

  @Override
  public SSAResult visitAssertStmt(SimpleCParser.AssertStmtContext ctx) {
    SSAResult result = new SSAResult();
    SSAResult expr = visit(ctx.condition);
    String condition = guard.peek();
    if (condition.length() > 0) {
      result.appendCode("assert (");
      result.appendCode(condition);
      result.appendCode(") ? ");
      result.appendCode(expr.getCode());
      result.appendCode(" : 1");
    } else {
      result.appendCode("assert ");
      result.appendCode(expr.getCode());
    }
    result.appendCode(";");
    return result;
  }

  @Override
  public SSAResult visitAssumeStmt(SimpleCParser.AssumeStmtContext ctx) {
    SSAResult result = new SSAResult();
    result.appendCode("assume ");
    SSAResult expr = visit(ctx.condition);
    result.appendCode(";");
    return result;
  }

  @Override
  public SSAResult visitHavocStmt(SimpleCParser.HavocStmtContext ctx) {
    /* TODO: fucked up for global variables!!!! */
    shouldModify = true;
    SSAResult result = new SSAResult();
    shouldModify = false;
    return result;
  }

  @Override
  public SSAResult visitCallStmt(SimpleCParser.CallStmtContext ctx) {
    //TODO: implement!
    return new SSAResult();
  }

  @Override
  public SSAResult visitIfStmt(SimpleCParser.IfStmtContext ctx) {
    Map<String, Integer> modifiedSetThenBlock;
    Map<String, Integer> modifiedSetElseBlock = new HashMap<String, Integer>();
    Map<String, Integer> currentIndexes = new HashMap<String, Integer>();

    SSAResult result = new SSAResult();
    SSAResult thenBlock;
    SSAResult elseBlock;
    String condition = visit(ctx.condition).getCode().toString();

    /* Visit then block. */
    beginScope(ScopeType.IF_ELSE_BRANCH, condition);
    result.appendCode("\n");
    result.appendCode(indent.getIndent());
    result.appendCode("// Guard: " + condition + "\n");
    thenBlock = visit(ctx.thenBlock);
    result.appendCode(thenBlock.getCode());
    modifiedSetThenBlock = endScope();
    for (Map.Entry<String, Integer> update : modifiedSetThenBlock.entrySet()) {
      String varName = update.getKey();
      currentIndexes.put(varName, scopes.getCurrentIndex(varName));
    }

    if (ctx.elseBlock != null) {
      /* Visit the else block. */
      beginScope(ScopeType.IF_ELSE_BRANCH, "!(" + condition + ")");
      result.appendCode(indent.getIndent());
      result.appendCode("// Guard: " + "!(" + condition + ")\n");
      result.appendCode(indent.getIndent());
      elseBlock = visit(ctx.elseBlock);
      result.appendCode(elseBlock.getCode());
      modifiedSetElseBlock = endScope();
      for (Map.Entry<String, Integer> update :
          modifiedSetElseBlock.entrySet()) {
        String varName = update.getKey();
        currentIndexes.put(varName, scopes.getCurrentIndex(varName));
      }
    }

    for (Map.Entry<String, Integer> entry : currentIndexes.entrySet()) {
      String varName = entry.getKey();
      int indexThen = modifiedSetThenBlock.containsKey(varName) ?
                        modifiedSetThenBlock.get(varName) :
                        scopes.getCurrentIndex(varName),
          indexElse = modifiedSetElseBlock.containsKey(varName) ?
                        modifiedSetElseBlock.get(varName) :
                        scopes.getCurrentIndex(varName),
          newIndex  = scopes.updateVariable(varName);
      result.appendCode("\n" + indent.getIndent() + varName + newIndex + " = (" + condition + ") ? " +
          varName + indexThen + " : " + varName + indexElse + ";");
    }

    return result;
  }

  @Override
  public SSAResult visitWhileStmt(SimpleCParser.WhileStmtContext ctx) {
    //TODO: implement
    return new SSAResult();
  }

  @Override
  public SSAResult visitBlockStmt(SimpleCParser.BlockStmtContext ctx) {
    SSAResult result = new SSAResult();
    beginScope(ScopeType.NORMAL, "");
    result.appendCode("\n");
    result.appendCode(indent.getIndent());
    result.appendCode("// Block statement begins:\n");
    SSAResult block = visitStatements(ctx.stmts);
    result.appendCode(block.getCode());
    result.appendCode(indent.getIndent());
    result.appendCode("// Block statement ends!\n");
    endScope();
    return result;
  }

  @Override
  public SSAResult visitLoopInvariant(SimpleCParser.LoopInvariantContext ctx) {
    //TODO:
    return new SSAResult();
  }

  @Override
  public SSAResult visitCandidateInvariant(
      SimpleCParser.CandidateInvariantContext ctx) {
    //TODO:
    return new SSAResult();
  }

  @Override
  public SSAResult visitTernExpr(SimpleCParser.TernExprContext ctx) {
    if (ctx.single != null) {
      return visit(ctx.single);
    }
    Iterator<SimpleCParser.LorExprContext> it = ctx.args.iterator();
    SSAResult result = visit(it.next());
    SSAResult expr;
    while (it.hasNext()) {
      expr = visit(it.next());
      result.appendCode(" ? ");
      result.appendCode(expr.getCode());

      expr = visit(it.next());
      result.appendCode(" : ");
      result.appendCode(expr.getCode());
    }
    return result;
  }

  @Override
  public SSAResult visitLorExpr(SimpleCParser.LorExprContext ctx) {
    if (ctx.single != null) {
      return visit(ctx.single);
    }
    return visitBinaryExpression(ctx.args, ctx.ops);
  }

  @Override
  public SSAResult visitLandExpr(SimpleCParser.LandExprContext ctx) {
    if (ctx.single != null) {
      return visit(ctx.single);
    }
    return visitBinaryExpression(ctx.args, ctx.ops);
  }

  @Override
  public SSAResult visitBorExpr(SimpleCParser.BorExprContext ctx) {
    if (ctx.single != null) {
      return visit(ctx.single);
    }
    return visitBinaryExpression(ctx.args, ctx.ops);
  }

  @Override
  public SSAResult visitBxorExpr(SimpleCParser.BxorExprContext ctx) {
    if (ctx.single != null) {
      return visit(ctx.single);
    }
    return visitBinaryExpression(ctx.args, ctx.ops);
  }

  @Override
  public SSAResult visitBandExpr(SimpleCParser.BandExprContext ctx) {
    if (ctx.single != null) {
      return visit(ctx.single);
    }
    return visitBinaryExpression(ctx.args, ctx.ops);
  }

  @Override
  public SSAResult visitEqualityExpr(SimpleCParser.EqualityExprContext ctx) {
    if (ctx.single != null) {
      return visit(ctx.single);
    }
    return visitBinaryExpression(ctx.args, ctx.ops);
  }

  @Override
  public SSAResult visitRelExpr(SimpleCParser.RelExprContext ctx) {
    if (ctx.single != null) {
      return visit(ctx.single);
    }
    return visitBinaryExpression(ctx.args, ctx.ops);
  }

  @Override
  public SSAResult visitShiftExpr(SimpleCParser.ShiftExprContext ctx) {
    if (ctx.single != null) {
      return visit(ctx.single);
    }
    return visitBinaryExpression(ctx.args, ctx.ops);
  }

  @Override
  public SSAResult visitAddExpr(SimpleCParser.AddExprContext ctx) {
    if (ctx.single != null) {
      return visitChildren(ctx);
    }
    return visitBinaryExpression(ctx.args, ctx.ops);
  }

  @Override
  public SSAResult visitMulExpr(SimpleCParser.MulExprContext ctx) {
    if (ctx.single != null) {
      return visit(ctx.single);
    }
    Iterator<SimpleCParser.UnaryExprContext> unaryExprIt = ctx.args.iterator();
    Iterator<Token> opsIt = ctx.ops.iterator();
    SSAResult result = visit(unaryExprIt.next());
    while (unaryExprIt.hasNext()) {
      SSAResult unaryExpr = visit(unaryExprIt.next());
      result.appendCode(" ");
      result.appendCode(opsIt.next().getText());
      result.appendCode(" ");
      result.appendCode(unaryExpr.getCode());
    }
    return result;
  }

  @Override
  public SSAResult visitUnaryExpr(SimpleCParser.UnaryExprContext ctx) {
    if (ctx.single != null) {
      return visit(ctx.single);
    }
    SSAResult result = new SSAResult();
    for (Token ops : ctx.ops) {
      if (ops.getText().equals("!") || ops.getText().equals("~")) {
        result.appendCode(ops.getText());
      }
    }
    SSAResult aux = visit(ctx.arg);
    result.appendCode(aux.getCode());
    return result;
  }

  @Override
  public SSAResult visitNumberExpr(SimpleCParser.NumberExprContext ctx) {
    SSAResult result = new SSAResult();
    result.appendCode(ctx.number.getText());
    return result;
  }

  @Override
  public SSAResult visitParenExpr(SimpleCParser.ParenExprContext ctx) {
    SSAResult result = new SSAResult();
    SSAResult expr = visit(ctx.arg);
    result.appendCode("(");
    result.appendCode(expr.getCode());
    result.appendCode(")");
    return result;
  }

  @Override
  public SSAResult visitResultExpr(SimpleCParser.ResultExprContext ctx) {
    SSAResult result = new SSAResult();
    result.appendCode(returnVariable + scopes.getCurrentIndex(returnVariable));
    return result;
  }

  @Override
  public SSAResult visitOldExpr(SimpleCParser.OldExprContext ctx) {
    SSAResult result = new SSAResult();
    String varName = ctx.arg.ident.name.getText();
    result.appendCode(varName + "0");
    return result;
  }

  @Override
  public SSAResult visitVarIdentifier(SimpleCParser.VarIdentifierContext ctx) {
    SSAResult result = new SSAResult();
    String varName = ctx.name.getText();
    int index;
    if (shouldModify) {
      index = scopes.updateVariable(varName);
    } else {
      index = scopes.getCurrentIndex(varName);
    }
    result.appendCode(varName + index);
    return result;
  }

  @Override
  protected SSAResult aggregateResult(SSAResult aggregate,
                                      SSAResult nextResult) {
    if (aggregate == null) {
      return nextResult;
    } else if (nextResult == null) {
      return aggregate;
    }
    aggregate.appendCode(nextResult.getCode());
    return aggregate;
  }
}
