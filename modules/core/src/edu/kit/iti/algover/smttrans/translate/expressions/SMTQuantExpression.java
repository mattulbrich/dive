package edu.kit.iti.algover.smttrans.translate.expressions;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;

import edu.kit.iti.algover.smttrans.data.Operation;
import edu.kit.iti.algover.smttrans.translate.Dependency;
import edu.kit.iti.algover.smttrans.translate.Type;
import edu.kit.iti.algover.util.Pair;

public class SMTQuantExpression extends SMTExpression {

    private SMTExpression qVar;
    private SMTExpression formula;
    
    public SMTQuantExpression(Operation op, Type type, SMTExpression qvar, SMTExpression formula) {
        super(op, type);
        this.qVar = qvar;
        this.formula = formula;

    }

    @Override
    public Pair<LinkedHashSet<Dependency>, String> toPSMT() {
        StringBuilder sb = new StringBuilder();
        LinkedHashSet<Dependency> set = new LinkedHashSet<>();
        sb.append("(");
        sb.append(op.toSMTLib(type));
        sb.append("(");
        sb.append(qVar.toPSMT().snd);
        sb.append(")");
        sb.append(formula.toPSMT().snd);
       // sb.append(")");
        String smt = sb.toString();
        return new Pair<LinkedHashSet<Dependency>, String>(set,smt.substring(0,smt.length()-2)); //delete last parantheses
    }

}
