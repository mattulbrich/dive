/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.term.*;
import edu.kit.iti.algover.term.QuantTerm.Quantifier;

public class TermBuilder {

    public final Term zero;

    private final SymbolTable symbolTable;

    public TermBuilder(SymbolTable symbolTable) {
        this.symbolTable = symbolTable;
        this.zero = intLiteral(0);
    }

    public final Term negate(Term t) throws TermBuildException {
        return new ApplTerm(BuiltinSymbols.NOT, t);
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
        FunctionSymbol eq = symbolTable.getFunctionSymbol("$eq<" + s + ">");
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

    public Term self() throws TermBuildException {
        return cons("this");
    }



    public Term makeFieldConst(String clazz, String field) throws TermBuildException {
        return cons(fieldName(clazz, field));
    }

    // FIXME TODO REVIEW change this to "field$" + clazz + "$" + field
    public static String fieldName(String clazz, String field) {
        return clazz + "$$" + field;
    }

    public Term selectField(Term heap, Term recv, Term field) throws TermBuildException {
        FunctionSymbol select =
                symbolTable.getFunctionSymbol(BuiltinSymbols.SELECT,
                        recv.getSort(),
                        field.getSort().getArguments().get(1));
        return new ApplTerm(select, heap, recv, field);
    }

    public Term selectArray(Term heap, Term array, Term index) throws TermBuildException {
        FunctionSymbol select =
                symbolTable.getFunctionSymbol(
                    BuiltinSymbols.ARRAY_SELECT,
                        array.getSort().getArguments().get(0));

        return new ApplTerm(select, heap, array, index);
    }

    public Term msNumOccOf(Term msTerm, Term valueTerm) throws TermBuildException{
        Sort seqSort = msTerm.getSort();
        assert seqSort.getName().equals("multiset");
        Sort elementSort = seqSort.getArguments().get(0);
        FunctionSymbol msOcc =
                symbolTable.getFunctionSymbol(BuiltinSymbols.MULTI_COUNT, elementSort);

        return new ApplTerm(msOcc, valueTerm, msTerm);
    }

    public Term selectArray2(ApplTerm heap, Term array, Term index0, Term index1) throws TermBuildException {
        FunctionSymbol select =
                symbolTable.getFunctionSymbol(
                    BuiltinSymbols.ARRAY2_SELECT,
                        array.getSort().getArguments().get(0));

        return new ApplTerm(select, heap, array, index0, index1);
    }

    public Term heap() throws TermBuildException {
        return new ApplTerm(BuiltinSymbols.HEAP);
    }

    public Term storeField(Term heapTerm, Term object, Term field, Term value) throws TermBuildException {
        Sort fieldSort = field.getSort();
        Sort classSort = fieldSort.getArguments().get(0);
        Sort valueSort = fieldSort.getArguments().get(1);
        FunctionSymbol store =
                symbolTable.getFunctionSymbol(BuiltinSymbols.STORE,
                        classSort, valueSort);

        return new ApplTerm(store, heapTerm, object, field, value);
    }

    public Term storeArray(Term heap, Term object, Term index, Term value) throws TermBuildException {
        Sort arraySort = object.getSort();
        assert arraySort.getName().equals("array");
        Sort elementSort = arraySort.getArguments().get(0);
        FunctionSymbol store =
                symbolTable.getFunctionSymbol(
                        BuiltinSymbols.ARRAY_STORE,
                        elementSort);

        return new ApplTerm(store, heap, object, index, value);
    }

    public Term storeArray2(Term heap, Term object, Term index, Term index2, Term value) throws TermBuildException {
        Sort arraySort = object.getSort();
        assert arraySort.getName().equals("array2");
        Sort elementSort = arraySort.getArguments().get(0);
        FunctionSymbol store =
                symbolTable.getFunctionSymbol(BuiltinSymbols.ARRAY2_STORE,
                        elementSort);

        return new ApplTerm(store, heap, object, index, index2, value);
    }

    public Term _null() throws TermBuildException {
        return new ApplTerm(BuiltinSymbols.NULL);
    }

    public Term seqLen(Term seqTerm) throws TermBuildException {
        Sort seqSort = seqTerm.getSort();
        assert seqSort.getName().equals("seq");
        Sort elementSort = seqSort.getArguments().get(0);
        FunctionSymbol seqlen =
                symbolTable.getFunctionSymbol(BuiltinSymbols.SEQ_LEN, elementSort);

        return new ApplTerm(seqlen, seqTerm);
    }

    public Term seqGet(Term seqTerm, Term indexTerm) throws TermBuildException {
        Sort seqSort = seqTerm.getSort();
        assert seqSort.getName().equals("seq");
        Sort elementSort = seqSort.getArguments().get(0);
        FunctionSymbol seqget =
                symbolTable.getFunctionSymbol(BuiltinSymbols.SEQ_GET, elementSort);

        return new ApplTerm(seqget, seqTerm, indexTerm);
    }

    public Term seqUpd(Term seqTerm, Term indexTerm, Term value) throws TermBuildException {
        Sort seqSort = seqTerm.getSort();
        assert seqSort.getName().equals("seq");
        Sort elementSort = seqSort.getArguments().get(0);
        FunctionSymbol sequpd =
                symbolTable.getFunctionSymbol(BuiltinSymbols.SEQ_UPDATE, elementSort);

        return new ApplTerm(sequpd, seqTerm, indexTerm, value);
    }

    public Term seqSub(Term seqTerm, Term from, Term to) throws TermBuildException {
        Sort seqSort = seqTerm.getSort();
        assert seqSort.getName().equals("seq");
        Sort elementSort = seqSort.getArguments().get(0);
        FunctionSymbol seqsub =
                symbolTable.getFunctionSymbol(BuiltinSymbols.SEQ_SUB, elementSort);

        return new ApplTerm(seqsub, seqTerm, from, to);
    }

    public Term fresh(Term oldheap, Term newheap, Term object) throws TermBuildException {
        ApplTerm o = new ApplTerm(BuiltinSymbols.IS_CREATED, oldheap, object);
        ApplTerm n = new ApplTerm(BuiltinSymbols.IS_CREATED, newheap, object);
        return and(negate(o), n);
    }

    public Term arrayToSeq(Term heapTerm, Term arrayTerm) throws TermBuildException {
        assert arrayTerm.getSort().getName().equals("array");
        Sort inst = arrayTerm.getSort().getArgument(0);
        FunctionSymbol f = symbolTable.getFunctionSymbol(BuiltinSymbols.ARRAY_TO_SEQ, inst);
        return new ApplTerm(f, heapTerm, arrayTerm);
    }

    public Term anyTerm() {
        return SchemaVarTerm.newUnnamedInstance();
    }
}
