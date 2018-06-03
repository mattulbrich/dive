package edu.kit.iti.algover.smttrans.translate.expressions;

import java.util.LinkedHashSet;

import edu.kit.iti.algover.smttrans.data.Operation;
import edu.kit.iti.algover.smttrans.translate.Dependency;
import edu.kit.iti.algover.util.Pair;

public class SMTVarExpression extends SMTExpression {

    private String name;
    private SMTExpression partner;

    public SMTVarExpression(String name, SMTExpression partner) {
        super(Operation.VAR);
        this.name = name;
        this.partner = partner;
    }

    @Override
    public Pair<LinkedHashSet<Dependency>, String> toPSMT() {
        StringBuilder sb = new StringBuilder();
        LinkedHashSet<Dependency> set = new LinkedHashSet<>();
        sb.append("(");
        sb.append(Operation.EQ.toSMTLib(type));
        sb.append(" ");
        sb.append(this.name);
        sb.append(" ");
        sb.append(partner.toPSMT().snd);
        sb.append(")");
        return new Pair<LinkedHashSet<Dependency>, String>(set,sb.toString());
    }

}
