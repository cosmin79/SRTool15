package tool;

import java.lang.StringBuilder;
import java.util.Map;
import java.util.HashMap;

public class SSAResult {

  private StringBuilder code;
  private Map<String, Integer> changed;

  public SSAResult() {
    code = new StringBuilder();
    changed = new HashMap<String, Integer>();
  }
}
