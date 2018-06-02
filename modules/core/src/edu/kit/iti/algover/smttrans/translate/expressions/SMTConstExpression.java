package edu.kit.iti.algover.smttrans.translate.expressions;

import java.util.ArrayList;
import java.util.List;

import edu.kit.iti.algover.smttrans.data.Operation;
import edu.kit.iti.algover.smttrans.translate.Type;

public class SMTConstExpression extends SMTExpression {

    private String name;

    public SMTConstExpression(String name, Type type) {
        super("$const", type, new ArrayList<>());
        this.name = name;

    }

    @Override
    public String toPSMT() { //TODO unique null
        

        return this.name;
    }

}
