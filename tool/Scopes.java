package tool;

import java.lang.StringBuilder;
import java.util.HashMap;
import java.util.ListIterator;
import java.util.Map;
import java.util.Stack;

public class Scopes {
  private Stack<Scope> scopes;
  private Map<String, Integer> maxIndex;
  private Map<String, Integer> lastIndex;
  private Map<String, Integer> nextIndex;

  public Scopes() {
    scopes    = new Stack<Scope>();
    maxIndex  = new HashMap<String, Integer>();
    lastIndex = new HashMap<String, Integer>();
    nextIndex = new HashMap<String, Integer>();
  }

  public void beginScope(ScopeType type) {
    scopes.push(new Scope(type));
  }

  public Map<String, Integer> endScope() {
    Scope scope = scopes.pop();
    switch (scope.getType()) {
      case NORMAL:
        scopes.peek().applyModifiedSet(scope.getModifiedVariablesSet());
        clearNewVariables(scope.getDefinedVariablesSet());
        break;
      case IF_ELSE_BRANCH:
        Map<String, Integer> modifiedSet = scope.getModifiedVariablesSet();
        Map<String, Integer> definedSet  = scope.getDefinedVariablesSet();
        for (Map.Entry<String, Integer> update : modifiedSet.entrySet()) {
          String varName = update.getKey();
          Integer index  = update.getValue();
          lastIndex.put(varName, getCurrentIndex(varName));
          nextIndex.put(varName, index + 1);
        }
        for (Map.Entry<String, Integer> update : definedSet.entrySet()) {
          String varName = update.getKey();
          Integer index  = getCurrentIndex(varName);
          if (index == Scope.NOT_PRESENT || !modifiedSet.containsKey(varName)) {
            lastIndex.put(varName, index);
            nextIndex.put(varName, index + 1);
          }
        }
        break;
    }
    return scope.getModifiedVariablesSet();
  }

  public int declareVariable(String varName) {
    int index = getFreshIndex(varName);
    Scope scope = scopes.peek();
    scope.declareVariable(varName, index);
    return index;
  }

  public int updateVariable(String varName) {
    int index = getFreshIndex(varName);
    Scope scope = scopes.peek();
    scope.updateVariable(varName, index);
    return index;
  }

  public int getCurrentIndex(String varName) {
    int index = Scope.NOT_PRESENT;
    ListIterator<Scope> it = scopes.listIterator(scopes.size());
    while (it.hasPrevious()) {
      int scopeIndex = it.previous().getIndex(varName);
      if (scopeIndex != Scope.NOT_PRESENT) {
        index = scopeIndex;
        break;
      }
    }
    return index;
  }

  public Map<String, Integer> getVariableDeclarations() {
    return maxIndex;
  }

  private int getFreshIndex(String varName) {
    int index;
    if (!maxIndex.containsKey(varName)) {
      index = 0;
      maxIndex.put(varName, index);
    } else {
      index = nextIndex.get(varName);
    }
    lastIndex.put(varName, index);
    nextIndex.put(varName, index + 1);
    if (index > maxIndex.get(varName)) {
      maxIndex.put(varName, index);
    }
    return index;
  }

  private void clearNewVariables(Map<String, Integer> newVariables) {
    for (Map.Entry<String, Integer> update : newVariables.entrySet()) {
      String varName = update.getKey();
      int index = getCurrentIndex(varName);
      lastIndex.put(varName, index);
      nextIndex.put(varName, index + 1);
    }
  }

  private class Scope {
    public static final int NOT_PRESENT = -1;

    private Map<String, Integer> oldVariables;
    private Map<String, Integer> newVariables;
    private final ScopeType      type;

    public Scope(ScopeType type) {
      this.type    = type;
      oldVariables = new HashMap<String, Integer>();
      newVariables = new HashMap<String, Integer>();
    }

    public void declareVariable(String varName, int index) {
      newVariables.put(varName, index);
    }

    public void updateVariable(String varName, int index) {
      if (newVariables.containsKey(varName) || index == NOT_PRESENT + 1) {
        /* If the variable was updated, but it has index = NOT_PRESENT + 1 it
         * means that it was not declared anywhere. */
        newVariables.put(varName, index);
        return;
      }
      oldVariables.put(varName, index);
    }

    public int getIndex(String varName) {
      if (newVariables.containsKey(varName)) {
        return newVariables.get(varName);
      } else if (oldVariables.containsKey(varName)) {
        return oldVariables.get(varName);
      }
      return NOT_PRESENT;
    }

    public ScopeType getType() {
      return type;
    }

    public boolean declared(String varName) {
      return newVariables.containsKey(varName);
    }

    public Map<String, Integer> getModifiedVariablesSet() {
      return oldVariables;
    }

    public Map<String, Integer> getDefinedVariablesSet() {
      return newVariables;
    }

    public void applyModifiedSet(Map<String, Integer> modifiedSet) {
      for (Map.Entry<String, Integer> update : modifiedSet.entrySet()) {
        String varName = update.getKey();
        Integer index  = update.getValue();
        if (newVariables.containsKey(varName)) {
          newVariables.put(varName, index);
        } else {
          oldVariables.put(varName, index);
        }
      }
    }
  }
}
