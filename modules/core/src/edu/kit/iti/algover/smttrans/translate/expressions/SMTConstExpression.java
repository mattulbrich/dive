package edu.kit.iti.algover.smttrans.translate.expressions;

import edu.kit.iti.algover.smttrans.data.Operation;
import edu.kit.iti.algover.smttrans.translate.Type;

public class SMTConstExpression extends SMTExpression {

    private String name;

    public SMTConstExpression(String name, Type type) {
        super(Operation.CONST, type);
        this.name = name;

    }

    public SMTConstExpression(String name) {
        super(Operation.CONST);
        this.name = name;
    }

    @Override
    public String toPSMT() { // TODO unique null

        return this.name + " ";
    }

}
