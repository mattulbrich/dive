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
        for (SMTExpression s : subs) {

            sb.append(s.toSMT(false));
        }
        sb.append(")");
        sb.append("\r\n");
        sb.append("(assert");
        if (inner instanceof SMTConstExpression) {
            sb.append(" (not ");
            sb.append(inner.toSMT(negate));
            sb.append("))");

        } else {

            sb.append(inner.toSMT(negate));
            sb.append(")");
        }
        ;
        return sb.toString();
    }

}
