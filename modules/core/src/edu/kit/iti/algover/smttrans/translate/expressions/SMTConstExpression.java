package edu.kit.iti.algover.smttrans.translate.expressions;

import java.util.LinkedHashSet;

import edu.kit.iti.algover.smttrans.data.Operation;
import edu.kit.iti.algover.smttrans.translate.Dependency;
import edu.kit.iti.algover.smttrans.translate.Type;
import edu.kit.iti.algover.util.Pair;

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
    public Pair<LinkedHashSet<Dependency>, String> toPSMT() { // TODO unique null

        return new Pair<LinkedHashSet<Dependency>, String>(null,this.name + " ");
    }

}
