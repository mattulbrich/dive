package edu.kit.iti.algover.smttrans.translate;

import java.util.List;

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

    @Override
    public String declare() {
        StringBuilder sb = new StringBuilder();
        sb.append("(declareFun");
        sb.append(show());
        sb.append(")");
        sb.append("\r\n");
        return sb.toString();    
    }
    
    

}
