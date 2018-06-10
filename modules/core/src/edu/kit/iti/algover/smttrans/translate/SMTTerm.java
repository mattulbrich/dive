package edu.kit.iti.algover.smttrans.translate;

import java.util.LinkedHashSet;
import java.util.List;

import edu.kit.iti.algover.smttrans.translate.expressions.SMTExpression;
import edu.kit.iti.algover.util.Pair;

public class SMTTerm {

    private SMTExpression expression;
//    private LinkedHashSet<Dependency> dependencies = new LinkedHashSet<>();
    private String psmt = "";

    public SMTTerm(SMTExpression e) {
        this.expression = e;
  //      Pair<LinkedHashSet<Dependency>, String> data = expression.toSMT();
   //     this.dependencies.addAll(data.fst);
      
       
        this.psmt = expression.toSMT();
    }

//    public LinkedHashSet<Dependency> getDependencies() {
//        return dependencies;
//    }

    public String toSMT() {
        StringBuilder sb = new StringBuilder();
        sb.append("\r\n");
        sb.append("(assert ");
        sb.append(this.psmt);
        sb.append(")");
      String result = sb.toString().replaceAll("\\s+(?=[),])", "").replace("$", ""); //TODO
      //  String result = sb.toString().replace("$", "");
       // return result.replaceAll("\\)+(?=[^\\)])", ") ");
      return result.toString();
    }
}
