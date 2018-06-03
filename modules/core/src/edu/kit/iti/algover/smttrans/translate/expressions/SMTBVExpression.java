package edu.kit.iti.algover.smttrans.translate.expressions;

import edu.kit.iti.algover.smttrans.data.Operation;
import edu.kit.iti.algover.smttrans.translate.Type;

public class SMTBVExpression extends SMTExpression {

    public SMTBVExpression(String name, Type t) {
        super(Operation.CONST, t);
     
    }

    @Override
    public String toPSMT() {
        StringBuilder sb = new StringBuilder();
        sb.append("(");
        sb.append(")");
        return sb.toString();
    }

}
