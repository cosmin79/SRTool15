package ast.visitor;

public interface Visitable {
    Object accept(Visitor visitor);
}
