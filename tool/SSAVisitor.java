package tool;

import parser.SimpleCBaseVisitor;
import parser.SimpleCParser;
import java.lang.String;
import java.util.Iterator;
import java.util.HashMap;
import java.util.Map;
import java.util.List;
import java.util.Stack;

public class SSAVisitor extends SimpleCBaseVisitor<SSAResult> {

  private Stack<Map<String, Integer>> fresher;

  public SSAVisitor(List<String> globalVaribles) {
    fresher = new Stack<Map<String, Integer>>();
    fresher.push(new HashMap<String, Integer>());
    for (String variable : globalVaribles) {
      fresher.peek().put(variable, 0);
    }
  }

  private void declareFunctionParams(SimpleCParser.ProcedureDeclContext ctx) {
    Iterator<SimpleCParser.FormalParamContext> it = ctx.formals.iterator();
    while (it.hasNext()) {
      SimpleCParser.FormalParamContext param = it.next();
      System.out.println("\t" + param.ident.ID());
    }
  }

  @Override
  public SSAResult visitProcedureDecl(SimpleCParser.ProcedureDeclContext ctx) {
    fresher.push(new HashMap<String, Integer>());
    declareFunctionParams(ctx);
    SSAResult result = visitChildren(ctx);
    fresher.pop();
    return result;
  }

  @Override
  public SSAResult visitVarIdentifier(SimpleCParser.VarIdentifierContext ctx) {
    return visitChildren(ctx);
  }
}
