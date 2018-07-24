package edu.kit.iti.algover.smttrans.translate.expressions;

import edu.kit.iti.algover.smttrans.data.Operation;
import edu.kit.iti.algover.smttrans.translate.ConstSignature;
import edu.kit.iti.algover.term.FunctionSymbol;

public class SMTVarExpression extends SMTExpression {

    
    private SMTExpression partner;

    public SMTVarExpression(FunctionSymbol fs, SMTExpression partner) {
        super(fs);
        this.partner = partner;
        this.sign = new ConstSignature(fs);
    }

    @Override
    public String toSMT(boolean... arg) {
        StringBuilder sb = new StringBuilder();
       // sb.append("(let ((");
       // sb.append(Operation.EQ.toSMT());
       // sb.append(" ");
       // sb.append("(");
        sb.append(sign.show());
        sb.append(" ");
        sb.append(partner.toSMT(arg));
       // sb.append(") ");
        return sb.toString();
    
       // (assert (let ((y (* x x))) (not(=> (> x 2) (> y 4)))))
    }

}
