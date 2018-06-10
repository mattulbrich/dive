package edu.kit.iti.algover.smttrans.translate.expressions;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import edu.kit.iti.algover.smttrans.translate.FuncSignature;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.util.Util;

public class SMTApplExpression extends SMTExpression {

    public SMTApplExpression(FunctionSymbol fs, List<SMTExpression> children) {
        super(fs, children);
        this.sign = new FuncSignature(fs);
    }

    @Override
    public String toSMT() {
        StringBuilder sb = new StringBuilder();
        sb.append("(");
        sb.append(sign.show() + " ");
        
        for (SMTExpression c : children) {
            sb.append(c.toSMT());
        }
        sb.append(") ");
        return sb.toString();

    }

}
