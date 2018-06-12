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
        if (quantifier == quantifier.EXISTS) {
            sb.append(Operation.EXISTS.toSMT());
        } else {
            sb.append(Operation.FORALL.toSMT());
        }
        sb.append("(");
        sb.append(qVar.toSMT(negate));
        sb.append(")");
        sb.append(formula.toSMT(negate).substring(0,formula.toSMT(negate).length()-4)); //delete last two parantheses
        sb.append(")");
        if (negate) {
            sb.append(")");
        }

        return sb.toString();
    }

}
