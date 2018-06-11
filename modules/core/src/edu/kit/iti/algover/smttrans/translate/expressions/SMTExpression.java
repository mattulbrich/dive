package edu.kit.iti.algover.smttrans.translate.expressions;

import java.util.ArrayList;
import java.util.List;

import edu.kit.iti.algover.smttrans.translate.Signature;
import edu.kit.iti.algover.term.FunctionSymbol;

public abstract class SMTExpression {
    protected FunctionSymbol fs;
    protected List<SMTExpression> children = new ArrayList<>();
    protected Signature sign;

    public abstract String toSMT();

    public SMTExpression(FunctionSymbol f, List<SMTExpression> c) {
        this.fs = f;
        this.children = c;
    }

public SMTExpression () {
    
}
    public SMTExpression(FunctionSymbol f) {
        this.fs = f;
    }
}
