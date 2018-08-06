package edu.kit.iti.algover.smttrans.translate;

import edu.kit.iti.algover.term.FunctionSymbol;

public class FuncSignature extends Signature{

    public FuncSignature(FunctionSymbol fs) {
        super(fs);
        
    }

    @Override
    public String show() {
        StringBuilder sb = new StringBuilder();
        String s = TypeContext.opToSMT(fs);
        
        sb.append(s);
        return sb.toString();
    }


    
    

}
