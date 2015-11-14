package ast;

import ast.visitor.Visitable;
import ast.visitor.Visitor;

import java.util.HashSet;
import java.util.Set;

public abstract class Node implements Visitable {

    private Set<String> modSet = new HashSet<>();

    public Node() {
        this.modSet = new HashSet<>();
    }

    public Set<String> getModSet() {
        return modSet;
    }

    public void addModSet(String varName) {
        modSet.add(varName);
    }

    public void addModSet(Node other) {
        modSet.addAll(other.getModSet());
    }
}
