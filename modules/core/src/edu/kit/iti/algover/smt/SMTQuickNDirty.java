/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */
// Checkstyle: ALLOFF
package edu.kit.iti.algover.smt;

import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.QuantTerm;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.TermVisitor;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.Util;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static edu.kit.iti.algover.smt.SExpr.Type.BOOL;
import static edu.kit.iti.algover.smt.SExpr.Type.UNIVERSE;

/*
 * This is a quick and dirty implementation -- just to get things going until the
 * real translation is operative.
 */
public class SMTQuickNDirty implements TermVisitor<Void, SExpr, RuntimeException> {

    private final static Map<String, String> ops = new HashMap<>();
    static {
        for(int i = 0; i < 100; i++) {
            ops.put("" + i, "" + i);
        }
        ops.put("$not", "not");
        ops.put("$and", "and");
        ops.put("$or", "or");
        ops.put("$imp", "=>");
        ops.put("$eq<int>", "=");
        ops.put("$lt", "<");
        ops.put("$le", "<=");
        ops.put("$ge", ">=");
        ops.put("$gt", ">");
        ops.put("$plus", "+");
        ops.put("$minus", "-");
        ops.put("$times", "*");
        ops.put("$seq_upd<int>", "sequpd");
        ops.put("$seq_len<int>", "seqlen");
        ops.put("$seq_get<int>", "seqget");
    }

    @Override
    public SExpr visit(VariableTerm variableTerm, Void arg) {
        return new SExpr("var$" + variableTerm.getName());
    }

    @Override
    public SExpr visit(QuantTerm term, Void arg) {
        String quantifier;
        switch (term.getQuantifier()) {
        case EXISTS:
            quantifier = "exists";
            break;
        case FORALL:
            quantifier = "forall";
            break;
        default:
            throw new UnsupportedOperationException("Unknown quantifier: " + term);
        }

        VariableTerm boundVar = term.getBoundVar();
        String varname = "var$" + boundVar.getName();

        SExpr qvar = new SExpr(varname, "Int");
        SExpr qqvar = new SExpr(qvar);
        SExpr formula = term.getTerm(0).accept(this, null);

        return new SExpr(quantifier, BOOL, qqvar, formula);
    }

    @Override
    public SExpr visit(ApplTerm applTerm, Void arg) {
        FunctionSymbol fs = applTerm.getFunctionSymbol();
        String n = fs.getName();
        String subs = ops.get(n);
        if(subs != null) {
            List<SExpr> children = Util.map(applTerm.getSubterms(), x -> x.accept(SMTQuickNDirty.this, null));
            return new SExpr(subs, children);
        }

        switch(n) {
        case "$seq_len<int>":
            return new SExpr("seqlen", applTerm.getTerm(0).accept(this, null));
        case "$seq_upd<int>":
            return new SExpr("store",
                    applTerm.getTerm(0).accept(this, null),
                    applTerm.getTerm(1).accept(this, null),
                    applTerm.getTerm(2).accept(this, null));
        default:
            if(fs.getArity() != 0)
                throw new UnsupportedOperationException(fs.toString());
            return new SExpr("pv$" + fs.getName());
        }
    }

    @Override
    public SExpr visit(LetTerm letTerm, Void arg) {

        SExpr inner = letTerm.getTerm(0).accept(this, arg);
        List<SExpr> substitutions = new ArrayList<SExpr>();
        for (Pair<VariableTerm, Term> pair : letTerm.getSubstitutions()) {
            substitutions.add(new SExpr("var$" + pair.fst.getName(), pair.snd.accept(this, null)));
        }
        return new SExpr("let", UNIVERSE, new SExpr(substitutions), inner);
    }
}
