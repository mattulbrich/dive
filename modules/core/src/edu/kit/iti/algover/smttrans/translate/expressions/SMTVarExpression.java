package edu.kit.iti.algover.smttrans.translate.expressions;

import edu.kit.iti.algover.smttrans.data.Operation;
import edu.kit.iti.algover.smttrans.translate.ConstSignature;
import edu.kit.iti.algover.smttrans.translate.FuncDependency;
import edu.kit.iti.algover.smttrans.translate.TypeContext;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;

public class SMTVarExpression extends SMTExpression {

    private SMTExpression partner;

    public SMTVarExpression(FunctionSymbol fs, SMTExpression partner) {
        super(fs);
        this.partner = partner;
        this.sign = new ConstSignature(fs);
    }

    @Override
    public String toSMT(boolean... arg) {
        StringBuilder sb = new StringBuilder();

        String s1 = TypeContext.normalizeReturnSort(fs);
        String s2 = TypeContext.normalizeReturnSort(partner.fs);

        if (!s1.equals(s2)) {
            
            
            String cast = "2o ";
            if (s1.contains("Set<Object>") || s2.contains("Set<Object>")) {
                cast = "2Set<Object> ";
                
            }
            System.out.println("S1 " + s1);
            
            System.out.println("S2 " + s2);
            
            if (s1.contains("Object")) {
                sb.append(sign.show());
            } else {
                sb.append("(" + s1 + cast);
                FuncDependency f = new FuncDependency(new FunctionSymbol(s1+cast.trim(), Sort.get("Set<Object>")));
                TypeContext.addToPreamble(f);
                sb.append(sign.show());
                sb.append(")");
            }
            sb.append(" ");
            if (s2.contains("Object")) {
                sb.append(partner.toSMT(arg));
            } else {
                sb.append("(" + s2 + cast);
                FuncDependency f = new FuncDependency(new FunctionSymbol(s2+cast.trim(), Sort.get("Set<Object>")));
                TypeContext.addToPreamble(f);
             
                sb.append(partner.toSMT(arg));
                sb.append(")");
            }
            
            
            
            sb.append(" ");
        } else {

            sb.append(sign.show());
            sb.append(" ");
            sb.append(partner.toSMT(arg));
        }

        return sb.toString();

    }

}
