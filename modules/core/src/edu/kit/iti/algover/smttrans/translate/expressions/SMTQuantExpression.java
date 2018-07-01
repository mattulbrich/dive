package edu.kit.iti.algover.smttrans.translate.expressions;

import edu.kit.iti.algover.smttrans.data.Operation;
import edu.kit.iti.algover.term.QuantTerm.Quantifier;

public class SMTQuantExpression extends SMTExpression {

    private SMTExpression qVar;
    private SMTExpression formula;
    private Quantifier quantifier;

    public SMTQuantExpression(Quantifier quantifier, SMTExpression qvar, SMTExpression formula) {
        super();
        this.quantifier = quantifier;
        this.qVar = qvar;
        this.formula = formula;

    }

    @Override
    public String toSMT(boolean negate) {
        StringBuilder sb = new StringBuilder();
        if (negate) {
            sb.append("(not ");
        }
        sb.append("(");
        if (quantifier == Quantifier.EXISTS) {
            sb.append(Operation.EXISTS.toSMT());
        } else {
            sb.append(Operation.FORALL.toSMT());
        }
        sb.append("(");
        sb.append(qVar.toSMT(false));
        sb.append(")");
        sb.append(formula.toSMT(false));
        sb.append(")");
        if (negate) {
            sb.append(")");
        }

        return sb.toString();
    }

}
