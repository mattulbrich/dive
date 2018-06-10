package edu.kit.iti.algover.smttrans.translate.expressions;

import java.util.LinkedHashSet;

import edu.kit.iti.algover.util.Pair;

public class SMTBVExpression extends SMTExpression {

    private String name;

    public SMTBVExpression(String name) {
        super();
        this.name = name;
    }

    @Override
    public String toSMT() {
        StringBuilder sb = new StringBuilder();

        sb.append("(");
        sb.append(this.name);
        sb.append(" ");

//        sb.append(type.toString());
        sb.append(")");
        return sb.toString();
    }
}
