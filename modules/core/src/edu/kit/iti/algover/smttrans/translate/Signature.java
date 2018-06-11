package edu.kit.iti.algover.smttrans.translate;

import edu.kit.iti.algover.term.FunctionSymbol;

public abstract class Signature {

    protected FunctionSymbol fs;
    
    
    public Signature(FunctionSymbol fs) {
        this.fs = fs;
    }
    
    
    
    public abstract String show();
}
