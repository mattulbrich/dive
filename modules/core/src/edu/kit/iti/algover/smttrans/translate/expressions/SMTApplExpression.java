package edu.kit.iti.algover.smttrans.translate.expressions;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

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
        String[] si = sign.show().split("<");
        String fu = "";
        if (si.length > 0)
            fu = si[0];

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

        } else if ((fu.equals(Operation.SETADD.toSMT()) || fu.equals(Operation.SETIN.toSMT()))
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
            boolean casts = false;
            Set<String> sorts = new HashSet<>();
            for (SMTExpression c : children) {
                String sort = TypeContext.normalizeReturnSort(c.fs);
                sorts.add(sort);
                if (sort.equalsIgnoreCase("object"))
                    casts = true;
              
                

            }
            if (sorts.size() > 1)
                casts = true;

            if (casts) {

                for (SMTExpression c : children) {
                    String sort = TypeContext.normalizeReturnSort(c.fs);
                    if (TypeContext.isBuiltIn(sort) || sort.equalsIgnoreCase("object")) {
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

            //

            // for (SMTExpression c : children) {
            // String sort = TypeContext.normalizeReturnSort(c.fs);
            // if (TypeContext.isBuiltIn(sort) || sort.equalsIgnoreCase("object")
            // || sort.toLowerCase().startsWith("set") ||
            // sort.toLowerCase().startsWith("seq")
            // || sort.toLowerCase().startsWith("arr") ||
            // sort.toLowerCase().startsWith("multiset")) {
            // sb.append(c.toSMT(false, bound));
            // continue;
            // }
            // sb.append("(" + sort + "2o ");
            //
            // sb.append(c.toSMT(false, bound));
            // sb.append(") ");
            // }
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
