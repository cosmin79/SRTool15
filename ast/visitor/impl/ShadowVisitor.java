package ast.visitor.impl;

import ast.Node;
import ast.Program;
import ast.VarDecl;
import parser.SimpleCParser;
import tool.ScopesHandler;
import tool.VariableIdsGenerator;

public class ShadowVisitor extends DefaultVisitor {

    private ScopesHandler scopesHandler;

    public ShadowVisitor(VariableIdsGenerator freshIds, Program program) {
        scopesHandler = new ScopesHandler(freshIds);
    }

    @Override
    public Node visit(Program program) {
        scopesHandler.pushStack();

        scopesHandler.popStack();
    }
}
