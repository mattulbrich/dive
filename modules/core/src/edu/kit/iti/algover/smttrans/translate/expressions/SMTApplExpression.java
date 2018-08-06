package edu.kit.iti.algover.smttrans.translate.expressions;

import java.util.List;

import edu.kit.iti.algover.smttrans.data.Operation;
import edu.kit.iti.algover.smttrans.translate.FuncSignature;
import edu.kit.iti.algover.smttrans.translate.TypeContext;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;

public class SMTApplExpression extends SMTExpression {

    public SMTApplExpression(FunctionSymbol fs, List<SMTExpression> children) {
        super(fs, children);
        this.sign = new FuncSignature(fs);
    }

    @Override
    public String toSMT(boolean... arg) {
        StringBuilder sb = new StringBuilder();
        boolean negate = false;
        boolean bound = false;
        if (arg.length > 0) {
            negate = arg[0];
        }
        if (arg.length > 1) {
            bound = arg[1];
        }

        if (negate)
            sb.append("(not ");
        sb.append("(");

        sb.append(sign.show() + " ");
        // TODO refactor to casts class

        if (sign.show().equals(Operation.CREATE.toSMT()) || sign.show().equals(Operation.ISCREATED.toSMT())) {
            for (SMTExpression c : children) {
                String sort = TypeContext.normalizeReturnSort(c.fs);
                if (TypeContext.isBuiltIn(sort) || sort.equalsIgnoreCase("object") || sort.equalsIgnoreCase("heap")) {
                    sb.append(c.toSMT(false, bound));
                    continue;
                }
                sb.append("(" + sort + "2o ");

                sb.append(c.toSMT(false, bound));
                sb.append(") ");
            }

        } else if ((sign.show().split("<")[0].equals(Operation.SETADD.toSMT())
                || sign.show().split("<")[0].equals(Operation.SETIN.toSMT()))
                && fs.getArgumentSorts().get(0).equals(Sort.OBJECT)) {

            for (SMTExpression c : children) {
                String sort = TypeContext.normalizeReturnSort(c.fs);
                if (sort.equalsIgnoreCase("object") || sort.equalsIgnoreCase("Set<Object>")) {
                    sb.append(c.toSMT(false, bound));
                    continue;
                }
                sb.append("(" + sort + "2o ");

                sb.append(c.toSMT(false, bound));
                sb.append(") ");
            }
        } else if (sign.show().equals(Operation.EQ.toSMT())) {

            for (SMTExpression c : children) {
                String sort = TypeContext.normalizeReturnSort(c.fs);
                if (TypeContext.isBuiltIn(sort) || sort.equalsIgnoreCase("object")
                        || sort.toLowerCase().startsWith("set") || sort.toLowerCase().startsWith("seq")
                        || sort.toLowerCase().startsWith("arr")) {
                    sb.append(c.toSMT(false, bound));
                    continue;
                }
                sb.append("(" + sort + "2o ");

                sb.append(c.toSMT(false, bound));
                sb.append(") ");
            }
        } else {
            for (SMTExpression c : children) {
                sb.append(c.toSMT(false, bound));
            }
        }
        if (negate)
            sb.append(")");
        sb.append(") ");

        return sb.toString();

    }

}
