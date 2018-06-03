package edu.kit.iti.algover.smttrans.translate.expressions;

import java.util.LinkedHashSet;
import java.util.List;

import edu.kit.iti.algover.smttrans.data.Operation;
import edu.kit.iti.algover.smttrans.translate.Dependency;
import edu.kit.iti.algover.smttrans.translate.Type;
import edu.kit.iti.algover.util.Pair;

public class SMTApplExpression extends SMTExpression{

    public SMTApplExpression(String op, Type type, List<SMTExpression> children) {
        super(op, type, children);
    }

    @Override
    public Pair<LinkedHashSet<Dependency>, String> toPSMT() {
        
        
        StringBuilder sb = new StringBuilder();
        sb.append("(");
        sb.append(op.toSMTLib(this.type) + " ");
        for (SMTExpression c : children) {
            sb.append(c.toPSMT().snd);
        }
        
        sb.append(") ");
        
        return new Pair<LinkedHashSet<Dependency>, String>(null,sb.toString());
        
    }

}
