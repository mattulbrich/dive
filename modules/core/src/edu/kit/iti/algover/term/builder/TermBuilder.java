/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.QuantTerm;
import edu.kit.iti.algover.term.QuantTerm.Quantifier;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.VariableTerm;

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
    public Term intLiteral(int val) {
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

    public Term lessEqual(Term term1, Term term2) throws TermBuildException {
        FunctionSymbol f = BuiltinSymbols.LE;
        return new ApplTerm(f, term1, term2);
    }

    public Term less(Term term1, Term term2) throws TermBuildException {
        FunctionSymbol f = BuiltinSymbols.LT;
        return new ApplTerm(f, term1, term2);
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

    public ApplTerm eq(Term lhs, Term rhs) throws TermBuildException {
        Sort s = lhs.getSort();
        FunctionSymbol eq = symbolTable.getFunctionSymbol("$eq[" + s + "]");
        return new ApplTerm(eq, lhs, rhs);
    }

    public Term id(String name) throws TermBuildException {
        FunctionSymbol f = symbolTable.getFunctionSymbol(name);
        if(f == null) {
            throw new TermBuildException("Unknown symbol: " + name);
        }
        return new ApplTerm(f);
    }

    public Term times(Term lhs, Term rhs) throws TermBuildException {
        return binary("$times", lhs, rhs);
    }

    public Term plus(Term lhs, Term rhs) throws TermBuildException {
        return binary("$plus", lhs, rhs);
    }

    private Term binary(String fct, Term lhs, Term rhs) throws TermBuildException {
        FunctionSymbol symbol = symbolTable.getFunctionSymbol(fct);
        if(symbol == null) {
            throw new Error("oh ... missing internal symbol " + fct);
        }
        return new ApplTerm(symbol, lhs, rhs);
    }

    public VariableTerm var(String varname, Sort sort) {
        return new VariableTerm(varname, sort);
    }

    public Term forall(VariableTerm var, Term matrix) throws TermBuildException {
        return new QuantTerm(Quantifier.FORALL, var, matrix);
    }

    public Term impl(Term lhs, Term rhs) throws TermBuildException {
        return binary("$imp", lhs, rhs);
    }

    public Term gt(Term lhs, Term rhs) throws TermBuildException {
        return binary("$gt", lhs, rhs);
    }

    public Term lt(Term lhs, Term rhs) throws TermBuildException {
        return binary("$lt", lhs, rhs);
    }

    public Term cons(String name) throws TermBuildException {
        FunctionSymbol symbol = symbolTable.getFunctionSymbol(name);
        if (symbol == null) {
            throw new TermBuildException("Unknown symbol " + name);
        }
        return new ApplTerm(symbol);
    }

}
