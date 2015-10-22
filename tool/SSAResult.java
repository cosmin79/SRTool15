package tool;

import java.lang.StringBuilder;
import java.util.Set;
import java.util.HashSet;

public class SSAResult {

  private StringBuilder code;
  private Set<String>   changed;

  public SSAResult() {
    code = new StringBuilder();
    changed = new HashSet<String>();
  }

  public void appendCode(String code) {
    this.code.append(code);
  }

  public void appendCode(StringBuilder code) {
    this.code.append(code);
  }

  public void changeVariable(String varName) {
    changed.add(varName);
  }

  public void changeVariables(Set<String> varNames) {
    changed.addAll(varNames);
  }

  public StringBuilder getCode() {
    return code;
  }

  public Set<String> getModifiedSet() {
    return changed;
  }

  @Override
  public String toString() {
    return code.toString();
  }
}
