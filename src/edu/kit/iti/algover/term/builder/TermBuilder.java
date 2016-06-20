/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;

public class TermBuilder {

    public final Term zero;

    private final SymbolTable symbolTable;

    public TermBuilder(SymbolTable symbolTable) {
        this.symbolTable = symbolTable;
        this.zero = intLiteral(0);
    }

    public final Term negate(Term t) throws TermBuildException {
        return new ApplTerm(BuiltinSymbols.NEG, t);
    }

    /**
     * Creates an integer literal.
     *
     * This is only possible for non-negative integers!
     *
     * @param val
     *            the value to make a term of
     * @return the term standing for the integer constant.
     */
    private Term intLiteral(int val) {
        FunctionSymbol l = symbolTable.getFunctionSymbol(Integer.toString(val));
        try {
            return new ApplTerm(l);
        } catch (TermBuildException e) {
            throw new Error(e);
        }
    }

    public final Term tt() throws TermBuildException {
        return new ApplTerm(BuiltinSymbols.TRUE);
    }

    public Term ff() throws TermBuildException {
        return new ApplTerm(BuiltinSymbols.FALSE);
    }

    public Term and(Term term1, Term term2) throws TermBuildException {
        if(term1.equals(tt())) {
            return term2;
        } else if(term2.equals(tt())) {
            return term1;
        } else {
            return new ApplTerm(BuiltinSymbols.AND, term1, term2);
        }
    }

    public Term lessEqual(Term zero2, Term term) throws TermBuildException {
        return tt();
    }

    public Term less(Term term, Term term2) throws TermBuildException {
        return tt();
    }

    public Term or(Term term1, Term term2) throws TermBuildException {
        if(term1.equals(ff())) {
            return term2;
        } else if(term2.equals(ff())) {
            return term1;
        } else {
            return new ApplTerm(BuiltinSymbols.OR, term1, term2);
        }
    }

}
