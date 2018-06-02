package edu.kit.iti.algover.smttrans.translate.expressions;

import java.util.List;

import edu.kit.iti.algover.smttrans.data.Operation;
import edu.kit.iti.algover.smttrans.translate.Type;

public class SMTApplExpression extends SMTExpression{

    public SMTApplExpression(String op, Type type, List<SMTExpression> children) {
        super(op, type, children);
    }

    @Override
    public String toPSMT() {
        
        
        StringBuilder sb = new StringBuilder();
        sb.append("(");
        sb.append(op.toSMTLib(this.type) + " ");
        for (SMTExpression c : children) {
            sb.append(c.toPSMT());
        }
        
        sb.append(") ");
        
        return sb.toString();
        
    }

}
