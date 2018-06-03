package edu.kit.iti.algover.smttrans.translate.expressions;

import java.util.ArrayList;

import edu.kit.iti.algover.smttrans.data.Operation;
import edu.kit.iti.algover.smttrans.translate.Type;

public class SMTVarExpression extends SMTExpression {

    private String name;
    private SMTExpression partner;

    public SMTVarExpression(String name, SMTExpression partner) {
        super(Operation.VAR);
        this.name = name;
        this.partner = partner;
    }

    @Override
    public String toPSMT() {
        StringBuilder sb = new StringBuilder();
        sb.append("(");
        sb.append(Operation.EQ.toSMTLib(type));
        sb.append(" ");
        sb.append(this.name);
        sb.append(" ");
        sb.append(partner.toPSMT());
        sb.append(")");
        sb.append(System.lineSeparator());
        return sb.toString();
    }

}
