package edu.kit.iti.algover.smttrans.translate.expressions;

import java.util.ArrayList;
import java.util.List;

import edu.kit.iti.algover.smttrans.data.Operation;
import edu.kit.iti.algover.smttrans.translate.Type;

public class SMTVarExpression extends SMTExpression{

    public SMTVarExpression(Operation op, Type type) {
        super(op, type, new ArrayList<>());

    }

    @Override
    public String toPSMT() {
        
        return null;
    }

}
