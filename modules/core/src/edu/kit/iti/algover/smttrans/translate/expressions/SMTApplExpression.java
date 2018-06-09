package edu.kit.iti.algover.smttrans.translate.expressions;

import java.util.LinkedHashSet;
import java.util.List;

import edu.kit.iti.algover.smttrans.data.Operation;
import edu.kit.iti.algover.smttrans.translate.Dependency;
import edu.kit.iti.algover.smttrans.translate.FuncDependency;
import edu.kit.iti.algover.smttrans.translate.Type;
import edu.kit.iti.algover.util.Pair;

public class SMTApplExpression extends SMTExpression{

    public SMTApplExpression(String op, Type type, List<SMTExpression> children) {
        super(op, type, children);
    }

    @Override
    public Pair<LinkedHashSet<Dependency>, String> toSMT() {
        
        LinkedHashSet<Dependency> set = new LinkedHashSet<>();
        FuncDependency d = new FuncDependency(op, type);
        set.add(d);
        
        StringBuilder sb = new StringBuilder();
        sb.append("(");
        sb.append(op.toSMTLib(this.type) + " ");
        for (SMTExpression c : children) {
            Pair<LinkedHashSet<Dependency>, String> cd = c.toSMT();
            set.addAll(cd.fst);
            sb.append(cd.snd);
        }
        
        sb.append(") ");
        
        return new Pair<LinkedHashSet<Dependency>, String>(set,sb.toString());
        
    }

}
