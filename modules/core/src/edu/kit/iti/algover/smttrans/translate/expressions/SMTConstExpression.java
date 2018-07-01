package edu.kit.iti.algover.smttrans.translate.expressions;

import edu.kit.iti.algover.smttrans.translate.ConstSignature;

import edu.kit.iti.algover.term.FunctionSymbol;


public class SMTConstExpression extends SMTExpression {


    public SMTConstExpression(FunctionSymbol fs) {
        super(fs);
        sign = new ConstSignature(fs);
          
    }


    @Override
    public String toSMT(boolean negate) {
        return sign.show() + " ";
    }

}
