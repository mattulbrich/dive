package edu.kit.iti.algover.smttrans.translate.expressions;

import java.util.ArrayList;

import edu.kit.iti.algover.smttrans.translate.Type;

public class SMTVarExpression extends SMTExpression {

    private String name;

    public SMTVarExpression(String name, Type type) { // TODO children ?
        super("$var", type, new ArrayList<>());
        this.name = name;
    }

    @Override
    public String toPSMT() {
        StringBuilder sb = new StringBuilder();
        sb.append("(");
        sb.append(this.name);
        sb.append(" ");
        sb.append(this.type.toString());
        sb.append(")");
        sb.append(System.lineSeparator());
        return sb.toString();
    }

}
