package edu.kit.iti.algover.smttrans.translate.expressions;

import java.util.List;

import edu.kit.iti.algover.smttrans.data.Operation;
import edu.kit.iti.algover.smttrans.translate.Type;

public class SMTQuantExpression extends SMTExpression{

    public SMTQuantExpression(Operation op, Type type, List<SMTExpression> children) {
        super(op, type, children);
        // TODO Auto-generated constructor stub
    }

    @Override
    public String toPSMT() {
        // TODO Auto-generated method stub
        return null;
    }

}
