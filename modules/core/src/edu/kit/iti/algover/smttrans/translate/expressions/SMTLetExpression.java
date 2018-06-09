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
    public Pair<LinkedHashSet<Dependency>, String> toSMT() {
        LinkedHashSet<Dependency> set = new LinkedHashSet<>();
        StringBuilder sb = new StringBuilder();
        for (SMTExpression s : subs) {
            Pair<LinkedHashSet<Dependency>, String> sp = s.toSMT();
            set.addAll(sp.fst);
            sb.append(sp.snd);
            //sb.append(s.toSMT().snd);
        }
        
        sb.append(")"); 
        sb.append("\r\n");
        sb.append("(assert"); //INNER
        Pair<LinkedHashSet<Dependency>, String> ip = inner.toSMT();
        set.addAll(ip.fst);
        sb.append(ip.snd);
        sb.append(")");
        //return sb.toString();
        return new Pair<LinkedHashSet<Dependency>, String>(set, sb.toString());
    }

}
