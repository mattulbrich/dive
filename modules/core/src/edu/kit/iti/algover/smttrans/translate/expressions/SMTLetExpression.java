package edu.kit.iti.algover.smttrans.translate.expressions;

import java.util.ArrayList;
import java.util.List;

import edu.kit.iti.algover.smttrans.data.Operation;
import edu.kit.iti.algover.smttrans.translate.Type;

public class SMTLetExpression extends SMTExpression {

    private SMTExpression inner;
    private List<SMTExpression> subs;

    public SMTLetExpression(List<SMTExpression> subs, SMTExpression inner) {
        super("$let", null, new ArrayList<>());
        this.subs = subs;
        this.inner = inner;
    }

    @Override
    public String toPSMT() {
        StringBuilder sb = new StringBuilder();
        for (SMTExpression s : subs) {
            sb.append(s.toPSMT());
        }
        sb.append(inner.toPSMT());
        return sb.toString();
    }

}
