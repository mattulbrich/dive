package edu.kit.iti.algover.smttrans.translate.expressions;

import java.util.LinkedHashSet;
import java.util.List;

import edu.kit.iti.algover.smttrans.data.Operation;
import edu.kit.iti.algover.smttrans.translate.Dependency;
import edu.kit.iti.algover.util.Pair;

public class SMTLetExpression extends SMTExpression {

    private SMTExpression inner;
    private List<SMTExpression> subs;

    public SMTLetExpression(List<SMTExpression> subs, SMTExpression inner) {
        super(Operation.LET);
        this.subs = subs;
        this.inner = inner;
    }

    @Override
    public Pair<LinkedHashSet<Dependency>, String> toPSMT() {
        
        StringBuilder sb = new StringBuilder();
        for (SMTExpression s : subs) {
            sb.append(s.toPSMT().snd);
        }
        sb.append(")");
        sb.append("(assert ");
        sb.append(inner.toPSMT().snd);
        sb.append(")");
        //return sb.toString();
        return new Pair<LinkedHashSet<Dependency>, String>(null, sb.toString());
    }

}
