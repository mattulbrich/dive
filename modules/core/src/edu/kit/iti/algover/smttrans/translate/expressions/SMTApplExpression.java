package edu.kit.iti.algover.smttrans.translate.expressions;

import java.util.List;

import edu.kit.iti.algover.term.FunctionSymbol;

public class SMTApplExpression extends SMTExpression{

    public SMTApplExpression(FunctionSymbol fs, List<SMTExpression> children) {
        super(fs, children);
    }

    @Override
    public String toSMT() {
        
        StringBuilder sb = new StringBuilder();
        

        
//        LinkedHashSet<Dependency> set = new LinkedHashSet<>();
//        FuncDependency d = new FuncDependency(op, type);
//        set.add(d);
//        
//        StringBuilder sb = new StringBuilder();
        sb.append("(");
//        sb.append(op.toSMTLib(this.type) + " ");
        sb.append(fs.getName());
        for (SMTExpression c : children) {
 //           Pair<LinkedHashSet<Dependency>, String> cd = c.toSMT();
//            set.addAll(cd.fst);
//            sb.append(cd.snd);
            sb.append(c.toSMT());
        }
//        
        sb.append(") ");
//        
//        return new Pair<LinkedHashSet<Dependency>, String>(set,sb.toString());
        
        return sb.toString();
        
    }

}
