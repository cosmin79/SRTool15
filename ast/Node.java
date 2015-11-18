package ast;

import ast.visitor.Visitable;
import ast.visitor.Visitor;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

public abstract class Node implements Visitable {

    private Set<String> modSet;

    private Set<Node> potentialFailures;

    private Set<WhileStmt> loops;

    public Node() {
        this.modSet = new HashSet<>();
        this.potentialFailures = new HashSet<>();
        this.loops = new HashSet<>();
    }

    public Set<String> getModSet() {
        return modSet;
    }

    public Set<Node> getPotentialFailures() {
        return potentialFailures;
    }

    public Set<WhileStmt> getLoops() {
        return loops;
    }

    public Set<Node> getPotentiallyCriticalFailures() {
        Set<Node> criticalFailures = new HashSet<>();
        for (Node potentialFailure: potentialFailures) {
            if ((potentialFailure instanceof AssertStmt) || (potentialFailure instanceof Precondition) ||
                    (potentialFailure instanceof Postcondition) || (potentialFailure instanceof Invariant)) {
                criticalFailures.add(potentialFailure);
            }
        }

        return criticalFailures;
    }

    public void addModSet(String varName) {
        modSet.add(varName);
    }

    public void addModSet(Node other) {
        modSet.addAll(other.getModSet());
    }

    public void addPotentialFailures(Node other) {
        potentialFailures.add(other);
    }

    public void addLoops(Node other) { loops.addAll(other.getLoops()); }

    public void addLoop(WhileStmt loop) { loops.add(loop); }
}
