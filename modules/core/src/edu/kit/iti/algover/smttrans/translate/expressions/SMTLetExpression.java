package edu.kit.iti.algover.smttrans.translate.expressions;

import java.util.List;

import edu.kit.iti.algover.smttrans.data.Operation;
import edu.kit.iti.algover.smttrans.translate.Type;

public class SMTLetExpression extends SMTExpression{

    public SMTLetExpression(String op, Type type, List<SMTExpression> children) {
        super(op, type, children);
        // TODO Auto-generated constructor stub
    }

    @Override
    public String toPSMT() {
       return "LET";
    }

}
