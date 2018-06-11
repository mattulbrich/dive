package edu.kit.iti.algover.smttrans.translate;

import edu.kit.iti.algover.term.FunctionSymbol;

public class ConstSignature extends Signature {

    public ConstSignature(FunctionSymbol fs) {
        super(fs);
        
    }

    @Override
    public String show() {
        StringBuilder sb = new StringBuilder();
        sb.append(fs.getName());
        return sb.toString();
    }

    @Override
    public String declare() {
        StringBuilder sb = new StringBuilder();
        sb.append("(declareConst");
        sb.append(show());
        sb.append(" ");
        sb.append(fs.getResultSort().getName());
        sb.append(")");
        sb.append("\r\n");
        return sb.toString();    
    }
    

}
