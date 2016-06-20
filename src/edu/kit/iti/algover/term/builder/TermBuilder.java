/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;

public class TermBuilder {

    public static final Term ZERO = intLiteral(0);

    public static final Term negate(Term t) throws TermBuildException {
        return new ApplTerm(BuiltinSymbols.NEG, t);
    }

    private static Term intLiteral(int i) {
        FunctionSymbol l = new FunctionSymbol(""+ i, Sort.INT);
        try {
            return new ApplTerm(l);
        } catch (TermBuildException e) {
            throw new Error(e);
        }
    }

    public static final Term tt() throws TermBuildException {
        return new ApplTerm(BuiltinSymbols.TRUE);
    }

    public static Term ff() throws TermBuildException {
        return new ApplTerm(BuiltinSymbols.FALSE);
    }

    public static Term and(Term term1, Term term2) throws TermBuildException {
        if(term1.equals(tt())) {
            return term2;
        } else if(term2.equals(tt())) {
            return term1;
        } else {
            return new ApplTerm(BuiltinSymbols.AND, term1, term2);
        }
    }

    public static Term lessEqual(Term zero2, Term term) throws TermBuildException {
        return tt();
    }

    public static Term less(Term term, Term term2) throws TermBuildException {
        return tt();
    }

    public static Term or(Term term1, Term term2) throws TermBuildException {
        if(term1.equals(ff())) {
            return term2;
        } else if(term2.equals(ff())) {
            return term1;
        } else {
            return new ApplTerm(BuiltinSymbols.OR, term1, term2);
        }
    }

}
