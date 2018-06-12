package edu.kit.iti.algover.smttrans.translate.expressions;

import java.util.List;

public class SMTLetExpression extends SMTExpression {

    private SMTExpression inner;
    private List<SMTExpression> subs;

    public SMTLetExpression(List<SMTExpression> subs, SMTExpression inner) {
        super();
        this.subs = subs;
        this.inner = inner;
    }

    @Override
    public String toSMT(boolean negate) {
        StringBuilder sb = new StringBuilder();
//        LinkedHashSet<Dependency> set = new LinkedHashSet<>();
//        StringBuilder sb = new StringBuilder();
        for (SMTExpression s : subs) {
            String sp = s.toSMT(negate);
            //set.addAll(sp.fst);
            sb.append(sp);
           // sb.append(s.toSMT());
       }
//        
        sb.append(")"); 
        sb.append("\r\n");
        sb.append("(assert"); //INNER
        String ip = inner.toSMT(negate);
//        set.addAll(ip.fst);
        sb.append(ip);
        sb.append(")");
//        //return sb.toString();
//        return new Pair<LinkedHashSet<Dependency>, String>(set, sb.toString());
        return sb.toString();
    }

}
