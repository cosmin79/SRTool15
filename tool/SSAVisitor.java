package tool;

import parser.SimpleCBaseVisitor;
import parser.SimpleCParser;
import java.lang.String;
import java.util.Iterator;
import java.util.ListIterator;
import java.util.HashMap;
import java.util.Map;
import java.util.List;
import java.util.Stack;

public class SSAVisitor extends SimpleCBaseVisitor<SSAResult> {

  private Stack<Map<String, Integer>> fresher;
  private Map<String, Integer>        variables;
  private boolean                     shouldModify;

  public SSAVisitor(List<String> globalVaribles) {
    fresher      = new Stack<Map<String, Integer>>();
    variables    = new HashMap<String, Integer>();
    shouldModify = false;
    fresher.push(new HashMap<String, Integer>());
    for (String variable : globalVaribles) {
      fresher.peek().put(variable, 0);
      variables.put(variable, 0);
    }
  }

  private int declareVariable(String varName) {
    int index = getNextFreeIndex(varName);
    if (variables.containsKey(varName)) {
      if (variables.get(varName) < index) {
        variables.put(varName, index);
      }
    } else {
      variables.put(varName, index);
    }
    fresher.peek().put(varName, index);
    return index;
  }

  private int updateVariable(String varName) {
    return findFreeIndex(varName, true);
  }

  private int getCurrentIndex(String varName, Map<String, Integer> map) {
    if (map == null) {
      return -1;
    } else {
      return map.get(varName);
    }
  }

  private Map<String, Integer> getMap(String varName) {
    ListIterator<Map<String, Integer>> it = fresher.listIterator(fresher.size());
    while (it.hasPrevious()) {
      Map<String, Integer> currentMap = it.previous();
      if (currentMap.containsKey(varName)) {
        return currentMap;
      }
    }
    return null;
  }

  private int getNextFreeIndex(String varName) {
    return findFreeIndex(varName, false);
  }

  private int findFreeIndex(String varName, boolean apply) {
    Map<String, Integer> map = getMap(varName);
    int index = getCurrentIndex(varName, map) + 1;
    if (map == null) {
      map = fresher.peek();
    }
    if (apply) {
      map.put(varName, index);
      if (variables.get(varName) < index) {
        variables.put(varName, index);
      }
    }
    return index;
  }

  private StringBuilder getDeclarations() {
    StringBuilder result = new StringBuilder();
    Iterator<Map.Entry<String, Integer>> it = variables.entrySet().iterator();
    while (it.hasNext()) {
      Map.Entry<String, Integer> entry = it.next();
      for (int k = 0; k <= entry.getValue(); k++) {
        result.append("int ").append(entry.getKey()).append(k).append(";\n");
      }
    }
    return result;
  }

  @Override
  public SSAResult visitProcedureDecl(SimpleCParser.ProcedureDeclContext ctx) {
    SSAResult program = visitChildren(ctx);
    StringBuilder declarations = getDeclarations();
    SSAResult result = new SSAResult();
    result.appendCode(declarations);
    result.appendCode(program.getCode());
    return result;
  }

  @Override
  public SSAResult visitFormalParam(SimpleCParser.FormalParamContext ctx) {
    shouldModify = true;
    SSAResult result = visitChildren(ctx);
    shouldModify = false;
    return result;
  }

  @Override
  public SSAResult visitVarIdentifier(SimpleCParser.VarIdentifierContext ctx) {
    String varName = ctx.name.getText();
    int index;
    if (shouldModify) {
      index = updateVariable(varName);
    } else {
      index = getCurrentIndex(varName, getMap(varName));
    }
    return new SSAResult();
  }

  @Override
  protected SSAResult aggregateResult(SSAResult aggregate,
                                      SSAResult nextResult) {
    if (aggregate == null) {
      return nextResult;
    } else if (nextResult == null) {
      return aggregate;
    }
    aggregate.changeVariables(nextResult.getModifiedSet());
    aggregate.appendCode(nextResult.getCode());
    return aggregate;
  }
}
