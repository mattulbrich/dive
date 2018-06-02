package edu.kit.iti.algover.smttrans.translate;

import java.util.List;

import edu.kit.iti.algover.smttrans.data.SMTContainer;
import edu.kit.iti.algover.smttrans.translate.expressions.SMTExpression;

public class SMTTerm {

    private SMTExpression expression;
    private List<Dependency> dependencies;

    public SMTTerm(SMTExpression e) {
        this.expression = e;
    }

    public List<Dependency> getDependencies() {
        return dependencies;
    }

//    public SMTContainer toPSMT() {
//        return null;
//    }

    
    //debug
    public String toPSMT() {
        return expression.toPSMT();
    }
}
