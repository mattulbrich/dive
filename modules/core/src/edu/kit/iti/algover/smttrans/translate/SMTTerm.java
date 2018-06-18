package edu.kit.iti.algover.smttrans.translate;

import java.util.LinkedHashSet;
import java.util.List;

import edu.kit.iti.algover.smttrans.translate.expressions.SMTExpression;
import edu.kit.iti.algover.util.Pair;

public class SMTTerm {

    private SMTExpression expression;

    public SMTTerm(SMTExpression e) {
        this.expression = e;

    }

    public String toSMT(boolean negate) {
        StringBuilder sb = new StringBuilder();
        sb.append("\r\n");
        sb.append("(assert ");
        sb.append(expression.toSMT(negate));
        sb.append(")");
        String result = sb.toString().replaceAll("\\s+(?=[),])", ""); // TODO .replace("$", "");
        return result.toString();
    }
}
