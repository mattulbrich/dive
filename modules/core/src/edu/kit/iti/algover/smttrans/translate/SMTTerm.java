package edu.kit.iti.algover.smttrans.translate;

import java.util.LinkedHashSet;
import java.util.List;

import edu.kit.iti.algover.smttrans.data.SMTContainer;
import edu.kit.iti.algover.smttrans.translate.expressions.SMTExpression;
import edu.kit.iti.algover.util.Pair;

public class SMTTerm {

    private SMTExpression expression;
    private LinkedHashSet<Dependency> dependencies = new LinkedHashSet<>();
    private String psmt = "";

    public SMTTerm(SMTExpression e) {
        this.expression = e;
        Pair<LinkedHashSet<Dependency>, String> data = expression.toPSMT();
        this.dependencies.addAll(data.fst);
        this.psmt = data.snd;
    }

    public LinkedHashSet<Dependency> getDependencies() {
        return dependencies;
    }

    public String toPSMT() {
        StringBuilder sb = new StringBuilder();
        sb.append("(assert ");
        sb.append(this.psmt);
        sb.append(")");
        String result = sb.toString().replaceAll("\\s+(?=[),])", "");
        return result.replaceAll("\\)+(?=[^\\)])", ") ");

    }
}
