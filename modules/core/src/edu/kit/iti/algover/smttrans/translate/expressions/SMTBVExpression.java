package edu.kit.iti.algover.smttrans.translate.expressions;

import edu.kit.iti.algover.smttrans.translate.VarSignature;
import edu.kit.iti.algover.term.FunctionSymbol;

public class SMTBVExpression extends SMTExpression {

   // private String name;
   // private Sort type;

    public SMTBVExpression(FunctionSymbol fs) {
        //FunctionSymbol fs = new FunctionSymbol(name, type);
        super(fs);
        this.sign = new VarSignature(fs);
    }

    @Override
    public String toSMT(boolean negate) {
        StringBuilder sb = new StringBuilder();

        sb.append("(");
        sb.append(sign.show());
        sb.append(")");
        return sb.toString();
    }
}
