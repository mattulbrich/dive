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
    public String toSMT(boolean... arg) {
        StringBuilder sb = new StringBuilder();
        sb.append("(let (");
        
        for (SMTExpression sub : subs) {           
            sb.append("(");
            sb.append(sub.toSMT(false));
            sb.append(")");
            
        }
        sb.append(") ");
        if (inner instanceof SMTConstExpression) {
            sb.append(" (not ");
            sb.append(inner.toSMT(arg));
            sb.append("))");

        } else {

            sb.append(inner.toSMT(arg));
            sb.append("))");
        }
        sb.append(")");
        return sb.toString();
    }
    


}
