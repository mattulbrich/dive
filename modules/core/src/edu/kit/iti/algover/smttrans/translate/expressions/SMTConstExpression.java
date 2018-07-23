package edu.kit.iti.algover.smttrans.translate.expressions;

import edu.kit.iti.algover.smttrans.translate.ConstSignature;
import edu.kit.iti.algover.smttrans.translate.TypeContext;
import edu.kit.iti.algover.term.FunctionSymbol;


public class SMTConstExpression extends SMTExpression {


    public SMTConstExpression(FunctionSymbol fs) {
        super(fs);
        sign = new ConstSignature(fs);
          
    }


    @Override
    public String toSMT(boolean...arg) {
        
        boolean bound = false;
        if (arg.length > 1) {
            bound = arg[1];
        }
        if (bound && TypeContext.isBV(fs)) {
            return fs.getName() + " ";
        }
        return sign.show() + " ";
    }

}
