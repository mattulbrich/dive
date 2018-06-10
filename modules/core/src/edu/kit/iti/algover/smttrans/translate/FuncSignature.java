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
        List<String> parts = TypeContext.typeOperation(fs.getName());
        for(String p : parts) {
            sb.append(p);
        }    
        return sb.toString();
    }

}
