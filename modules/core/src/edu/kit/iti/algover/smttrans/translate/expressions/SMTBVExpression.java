package edu.kit.iti.algover.smttrans.translate.expressions;

import java.util.LinkedHashSet;

import edu.kit.iti.algover.smttrans.translate.VarSignature;
import edu.kit.iti.algover.smttrans.translate.TypeContext;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.util.Pair;

public class SMTBVExpression extends SMTExpression {

   // private String name;
   // private Sort type;

    public SMTBVExpression(FunctionSymbol fs) {
        //FunctionSymbol fs = new FunctionSymbol(name, type);
        super(fs);
        this.sign = new VarSignature(fs);
    }

    @Override
    public String toSMT() {
        StringBuilder sb = new StringBuilder();

        sb.append("(");
        sb.append(sign.show());
        sb.append(")");
        return sb.toString();
    }
}
