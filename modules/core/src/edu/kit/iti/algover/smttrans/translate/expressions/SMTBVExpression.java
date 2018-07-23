package edu.kit.iti.algover.smttrans.translate.expressions;

import edu.kit.iti.algover.smttrans.translate.TypeContext;
import edu.kit.iti.algover.smttrans.translate.VarSignature;
import edu.kit.iti.algover.term.FunctionSymbol;

public class SMTBVExpression extends SMTExpression {



    public SMTBVExpression(FunctionSymbol fs) {
      
        super(fs);
        this.sign = new VarSignature(fs);
 
    }

    @Override
    public String toSMT(boolean... arg) {
        StringBuilder sb = new StringBuilder();
        TypeContext.addBV(fs);
        sb.append("(");
        sb.append(sign.show());
        sb.append(")");
        return sb.toString();
    }
}
