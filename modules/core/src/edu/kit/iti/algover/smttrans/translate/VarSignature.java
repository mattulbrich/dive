package edu.kit.iti.algover.smttrans.translate;

import edu.kit.iti.algover.term.FunctionSymbol;

public class VarSignature extends Signature {

    public VarSignature(FunctionSymbol fs) {
        super(fs);
    }

    @Override
    public String show() {
        StringBuilder sb = new StringBuilder();
        sb.append(fs.getName());

        sb.append(" ");
        sb.append(TypeContext.normalizeName(fs.getResultSort().getName()));
        return sb.toString();
    }


}
