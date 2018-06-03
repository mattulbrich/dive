package edu.kit.iti.algover.smttrans.translate;

import java.util.LinkedHashSet;
import java.util.List;

import edu.kit.iti.algover.smttrans.data.SMTContainer;
import edu.kit.iti.algover.smttrans.translate.expressions.SMTExpression;
import edu.kit.iti.algover.util.Pair;

public class SMTTerm {

    private SMTExpression expression;
    private List<Dependency> dependencies;

    public SMTTerm(SMTExpression e) {
        this.expression = e;
    }

    public List<Dependency> getDependencies() {
        return dependencies;
    }

//    public SMTContainer toPSMT() {
//        return null;
//    }

    
    //debug
    public String toPSMT() {
        
        Pair<LinkedHashSet<Dependency>, String> data = expression.toPSMT();
        for (Dependency d : data.fst) {
            System.out.println(d.toString());
        }
        StringBuilder sb = new StringBuilder();
        sb.append("(assert ");
        //sb.append(expression.toPSMT());
        sb.append(data.snd);
        sb.append(")");
        String result = sb.toString().replaceAll("\\s+(?=[),])", "");
        return result.replaceAll("\\)+(?=[^\\)])", ") ");
        
    }
}
