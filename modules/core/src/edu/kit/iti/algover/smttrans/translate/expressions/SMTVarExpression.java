package edu.kit.iti.algover.smttrans.translate.expressions;

import edu.kit.iti.algover.smttrans.data.Operation;
import edu.kit.iti.algover.smttrans.translate.CastDependency;
import edu.kit.iti.algover.smttrans.translate.ConstSignature;
import edu.kit.iti.algover.smttrans.translate.Dependency;
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

            if (s1.contains("Object")) {
                sb.append(sign.show());
            } else {
                sb.append("(" + s1 + cast);
                Dependency f = new CastDependency(new FunctionSymbol(s1 + cast.trim(), Sort.get("Set<Object>")), s1);
                TypeContext.addToPreamble(f);
                sb.append(sign.show());
                sb.append(")");
            }
            sb.append(" ");
            if (s2.contains("Object")) {
                sb.append(partner.toSMT(arg));
            } else {
                sb.append("(" + s2 + cast);
                Dependency f = new CastDependency(
                        new FunctionSymbol(s2 + cast.trim(), Sort.get("Set<Object>"), Sort.get(s2)), s2);

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
