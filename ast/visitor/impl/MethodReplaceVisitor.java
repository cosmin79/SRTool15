package ast.visitor.impl;

import ast.Node;
import ast.ProcedureDecl;
import ast.Program;
import ast.VarDecl;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;

// This could become more generic
public class MethodReplaceVisitor extends DefaultVisitor {

    private ProcedureDecl replacementMethod;

    public MethodReplaceVisitor(Map<Node, Node> predMap, ProcedureDecl replacementMethod) {
        super(predMap);
        this.replacementMethod = replacementMethod;
    }

    @Override
    public Object visit(Program program) {
        List<VarDecl> globals = new LinkedList<>();
        List<ProcedureDecl> procedures = new LinkedList<>();

        for (VarDecl varDecl: program.getVarDecls()) {
            globals.add((VarDecl) varDecl.accept(this));
        }

        for (ProcedureDecl procedureDecl: program.getProcedureDecls()) {
            if (procedureDecl.getMethodName().equals(replacementMethod.getMethodName())) {
                procedures.add(replacementMethod);
            } else {
                procedures.add((ProcedureDecl) procedureDecl.accept(this));
            }
        }

        return new Program(globals, procedures);
    }
}
