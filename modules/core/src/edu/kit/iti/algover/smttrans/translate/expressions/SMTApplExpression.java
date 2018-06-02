package edu.kit.iti.algover.smttrans.translate.expressions;

import java.util.List;

import edu.kit.iti.algover.smttrans.data.Operation;
import edu.kit.iti.algover.smttrans.translate.Type;

public class SMTApplExpression extends SMTExpression{

    public SMTApplExpression(Operation op, Type type, List<SMTExpression> children) {
        super(op, type, children);
        // TODO Auto-generated constructor stub
    }

    @Override
    public String toPSMT() {
        
        StringBuilder sb = new StringBuilder();
        sb.append("( ");
        sb.append(op.name() + " ");
        for (SMTExpression c : children) {
            sb.append(c.toPSMT());
        }
        return sb.toString();
        
    }

}
