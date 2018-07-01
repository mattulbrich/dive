package edu.kit.iti.algover.smttrans.translate;

import edu.kit.iti.algover.term.FunctionSymbol;

public class ConstSignature extends Signature {

    public ConstSignature(FunctionSymbol fs) {
        super(fs);
        
    }

    @Override
    public String show() {
        StringBuilder sb = new StringBuilder();
        sb.append(Names.toSMT(fs.getName()));
        return sb.toString();
    }



}
