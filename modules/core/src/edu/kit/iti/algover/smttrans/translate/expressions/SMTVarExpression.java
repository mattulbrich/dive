package edu.kit.iti.algover.smttrans.translate.expressions;

import edu.kit.iti.algover.smttrans.data.Operation;
import edu.kit.iti.algover.smttrans.translate.ConstSignature;
import edu.kit.iti.algover.term.FunctionSymbol;

public class SMTVarExpression extends SMTExpression {

    
    private SMTExpression partner;

    public SMTVarExpression(FunctionSymbol fs, SMTExpression partner) {
        super(fs);
        this.partner = partner;
        this.sign = new ConstSignature(fs);
    }

    @Override
    public String toSMT(boolean negate) {
        StringBuilder sb = new StringBuilder();
        // LinkedHashSet<Dependency> set = new LinkedHashSet<>();
        // set.add(new ConstDependency(this.name, new
        // Type(Type.typeConst(this.name).getName())));
        sb.append("(");
        sb.append(Operation.EQ.toSMT()); // TODO eq
        sb.append(" ");
        sb.append(sign.show());
        sb.append(" ");
        sb.append(partner.toSMT(negate));
        sb.append(") ");
        //
        // return new Pair<LinkedHashSet<Dependency>, String>(set,sb.toString());
        return sb.toString();
    }

}
