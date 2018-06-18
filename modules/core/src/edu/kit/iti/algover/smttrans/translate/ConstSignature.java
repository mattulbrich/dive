package edu.kit.iti.algover.smttrans.translate;

import edu.kit.iti.algover.term.FunctionSymbol;

public class ConstSignature extends Signature {

    public ConstSignature(FunctionSymbol fs) {
        super(fs);
        
    }

    @Override
    public String show() {
        StringBuilder sb = new StringBuilder();
//        System.out.println("NAME " + fs.getName());
        sb.append(Names.toSMT(fs.getName()));
//        System.out.println("Translation: " + Names.toSMT(fs.getName()));
   
        return sb.toString();
    }



}
