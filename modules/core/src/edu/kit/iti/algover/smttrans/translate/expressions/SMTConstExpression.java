package edu.kit.iti.algover.smttrans.translate.expressions;

public class SMTConstExpression extends SMTExpression {

    private String name;

    public SMTConstExpression(String name) {
        super();
        this.name = name;     
    }


    @Override
    public String toSMT() {
        return this.name + " ";
    }

}
