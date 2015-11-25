package ast;

import ast.visitor.Visitable;

import java.util.HashSet;
import java.util.Set;

public abstract class Node implements Visitable {

    private Set<String> modSet;

    private Set<Node> potentialFailures;

    private Set<WhileStmt> loops;

    private Set<CallStmt> callStms;

    public Node() {
        this.modSet = new HashSet<>();
        this.potentialFailures = new HashSet<>();
        this.loops = new HashSet<>();
        this.callStms = new HashSet<>();
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

    public Set<CallStmt> getCallStmts() {
        return callStms;
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

    public void addModSet(Set<String> modSet) {
        this.modSet.addAll(modSet);
    }

    public void addModSet(String varName) {
        modSet.add(varName);
    }

    public void addModSet(Node other) {
        modSet.addAll(other.getModSet());
    }

    public void addPotentialFailure(Node node) {
        potentialFailures.add(node);
    }

    public void addPotentialFailures(Node other) {
        potentialFailures.addAll(other.getPotentialFailures());
    }

    public void addLoops(Node other) { loops.addAll(other.getLoops()); }

    public void addLoop(WhileStmt loop) { loops.add(loop); }

    public void addCall(CallStmt callStmt) {
        callStms.add(callStmt);
    }

    public void addCalls(Node other) {
        callStms.addAll(other.getCallStmts());
    }
}
