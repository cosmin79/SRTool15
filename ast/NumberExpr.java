package ast;

public class NumberExpr extends AtomExpr {

    private Integer number;

    public NumberExpr(Integer number) {
        this.number = number;
    }

    public Integer getNumber() {
        return number;
    }
}
