package ast.visitor.impl;

import ast.*;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

// Given a set of candidate nodes, it replaces them with normal corresponding nodes
public class HoudiniVisitor extends DefaultVisitor {

    private Set<Node> candidates;

    public HoudiniVisitor(Map<Node, Node> predMap, Set<Node> candidates) {
        super(predMap);
        this.candidates = candidates;
    }

    @Override
    public Object visit(CandidatePrecondition candidatePrecondition) {
        if (candidates.contains(candidatePrecondition)) {
            Precondition newPrecondition
                    = new Precondition((Expr) candidatePrecondition.getCondition().accept(this));
            predMap.put(newPrecondition, candidatePrecondition);
            return newPrecondition;
        }

        return super.visit(candidatePrecondition);
    }

    @Override
    public Object visit(CandidatePostcondition candidatePostcondition) {
        if (candidates.contains(candidatePostcondition)) {
            Postcondition newPostcondition
                    = new Postcondition((Expr) candidatePostcondition.getCondition().accept(this));
            predMap.put(newPostcondition, candidatePostcondition);
            return newPostcondition;
        }

        return super.visit(candidatePostcondition);
    }

    @Override
    public Object visit(CandidateInvariant candidateInvariant) {
        if (candidates.contains(candidateInvariant)) {
            Invariant newInvariant = new Invariant((Expr) candidateInvariant.getCondition().accept(this), true);
            predMap.put(newInvariant, candidateInvariant);
            return newInvariant;
        }

        return super.visit(candidateInvariant);
    }
}
