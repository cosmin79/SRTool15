package ast;

import java.util.LinkedList;
import java.util.List;

public class Program extends Node {

    private List<VarDecl> varDecls = new LinkedList<>();

    private List<ProcedureDecl> procedureDecls = new LinkedList<>();

    public Program(List<VarDecl> varDecls, List<ProcedureDecl> procedureDecls) {
        this.varDecls = varDecls;
        this.procedureDecls = procedureDecls;
    }

    public List<VarDecl> getVarDecls() {
        return varDecls;
    }

    public List<ProcedureDecl> getProcedureDecls() {
        return procedureDecls;
    }
}
