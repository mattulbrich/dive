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
    public String toSMT(boolean... arg) {
        StringBuilder sb = new StringBuilder();
        boolean negate = false;
        boolean bound = false;
        if (arg.length > 0) {
            negate = arg[0];
        }
        if (arg.length > 1) {
            bound = arg[1];
        }
        
        if (negate)
            sb.append("(not");
        sb.append("(");
       
        sb.append(sign.show() + " ");
        
        for (SMTExpression c : children) {
            sb.append(c.toSMT(false,bound));
        }
        if(negate)
            sb.append(")");
        sb.append(") ");
        
        return sb.toString();

    }

}
