package edu.kit.iti.algover.smttrans.translate.expressions;

import java.util.ArrayList;
import java.util.List;

import edu.kit.iti.algover.smttrans.data.Operation;
import edu.kit.iti.algover.smttrans.translate.Type;

public class SMTQuantExpression extends SMTExpression {

    private SMTExpression qVar;
    private SMTExpression formula;
    
    public SMTQuantExpression(Operation op, Type type, SMTExpression qvar, SMTExpression formula) {
        super(op, type);
        this.qVar = qvar;
        this.formula = formula;

    }

    @Override
    public String toPSMT() {
        StringBuilder sb = new StringBuilder();
        sb.append("(");
        sb.append(op.toSMTLib(type));
        sb.append("(");
        sb.append(qVar.toPSMT());
        sb.append(")");
        sb.append(formula.toPSMT());
        sb.append(")");
        return sb.toString();
    }

}
