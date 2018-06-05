package edu.kit.iti.algover.smttrans.translate.expressions;

import java.util.LinkedHashSet;

import edu.kit.iti.algover.smttrans.data.Operation;
import edu.kit.iti.algover.smttrans.translate.Dependency;
import edu.kit.iti.algover.smttrans.translate.Type;
import edu.kit.iti.algover.util.Pair;

public class SMTBVExpression extends SMTExpression {

    private String name;
    private Type type;

    public SMTBVExpression(String name, Type type) {
        super(Operation.BV);
        this.name = name;
        this.type = type;
    }

    @Override
    public Pair<LinkedHashSet<Dependency>, String> toPSMT() {
        StringBuilder sb = new StringBuilder();
        LinkedHashSet<Dependency> set = new LinkedHashSet<>();
        sb.append("(");
        sb.append(this.name);
        sb.append(" ");
        //sb.append(partner.toPSMT().snd);
        sb.append(type.toString());
        sb.append(")");
        return new Pair<LinkedHashSet<Dependency>, String>(set,sb.toString());
    }
}
