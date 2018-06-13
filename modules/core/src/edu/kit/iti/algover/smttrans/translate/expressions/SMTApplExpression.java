package edu.kit.iti.algover.smttrans.translate.expressions;

import java.util.List;
import edu.kit.iti.algover.smttrans.translate.FuncSignature;
import edu.kit.iti.algover.term.FunctionSymbol;

public class SMTApplExpression extends SMTExpression {

    public SMTApplExpression(FunctionSymbol fs, List<SMTExpression> children) {
        super(fs, children);
        this.sign = new FuncSignature(fs);
    }

    @Override
    public String toSMT(boolean negate) {
        StringBuilder sb = new StringBuilder();
        if (negate)
            sb.append("(not");
        sb.append("(");
       
        sb.append(sign.show() + " ");
        
        for (SMTExpression c : children) {
            sb.append(c.toSMT(false)); //TODO correct ?
        }
        if(negate)
            sb.append(")");
        sb.append(") ");
        
        return sb.toString();

    }

}
