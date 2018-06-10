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
    public String toSMT() {
        StringBuilder sb = new StringBuilder();
        sb.append("(");
        if (quantifier == quantifier.EXISTS) {
            sb.append(Operation.EXISTS.toSMT());
        } else {
            sb.append(Operation.FORALL.toSMT());
        }
        sb.append("(");
        sb.append(qVar.toSMT());
        sb.append(")");
        sb.append(formula.toSMT());
        sb.append(")");
        // String smt = sb.toString();
        // return new Pair<LinkedHashSet<Dependency>,
        // String>(set,smt.substring(0,smt.length()-2)); //delete last parantheses
        return sb.toString();
    }

}
