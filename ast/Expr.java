package ast;

import java.util.List;
import java.util.Set;

public abstract class Expr extends Node {
    public abstract Set<String> getRefVars();

    public abstract Boolean isCandidateHoudini();

    public abstract List<Expr> getExprs();
}
