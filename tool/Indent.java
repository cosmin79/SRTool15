package tool;

import java.lang.String;

public class Indent {
  private String tab;
  private String indentation;
  private int    numberOfTabs;

  public Indent(String tab) {
    this.tab = tab;
    numberOfTabs = 0;
    indentation = null;
  }

  public void push() {
    numberOfTabs++;
    indentation = null;
  }

  public void pop() {
    numberOfTabs--;
    indentation = null;
  }

  public String getIndent() {
    if (indentation == null) {
      StringBuilder sb = new StringBuilder();
      for (int i = 1; i <= numberOfTabs; i++) {
        sb.append(tab);
      }
      indentation = sb.toString();
    }
    return indentation;
  }
}
