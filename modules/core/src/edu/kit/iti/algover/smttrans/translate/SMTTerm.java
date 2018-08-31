package edu.kit.iti.algover.smttrans.translate;

import edu.kit.iti.algover.smttrans.translate.expressions.SMTConstExpression;
import edu.kit.iti.algover.smttrans.translate.expressions.SMTExpression;

public class SMTTerm {

    private SMTExpression expression;

    public SMTTerm(SMTExpression e) {
        this.expression = e;

    }
    


    public String toSMT(boolean negate) {
        StringBuilder sb = new StringBuilder();
        sb.append("\r\n");
        sb.append("(assert ");
        if (expression instanceof SMTConstExpression && negate) { // term is a single boolean constant
            
    
            sb.append("(not ");
            sb.append(expression.toSMT(negate));
            sb.append("))");
        } else {
            
        
        
        
        sb.append(expression.toSMT(negate));
        sb.append(")");
        
        }
        String result = sb.toString().replaceAll("\\s+(?=[),])", "");
        return result;
        
        
    }
}
