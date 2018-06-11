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
        sb.append(
                fs.getResultSort().getName().substring(0, 1).toUpperCase() + fs.getResultSort().getName().substring(1));
        return sb.toString();
    }

    @Override
    public String declare() {
        StringBuilder sb = new StringBuilder();
        sb.append("(declareVar");
        sb.append(show());
        sb.append(")");
        sb.append("\r\n");
        return sb.toString();    
    }
}
