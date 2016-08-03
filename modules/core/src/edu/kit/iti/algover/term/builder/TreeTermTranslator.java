/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedList;
import java.util.List;

import edu.kit.iti.algover.SymbexStateToFormula;
import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.symbex.VariableMap;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.QuantTerm;
import edu.kit.iti.algover.term.QuantTerm.Quantifier;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.util.Pair;

/**
 * The Class TreeTermTranslator is used to create a {@link Term} object from a
 * {@link DafnyTree}.
 *
 * @see Term
 * @see DafnyTree
 *
 * @author Mattias Ulbrich
 */
public class TreeTermTranslator {

    private final SymbolTable symbolTable;

    private final Deque<VariableTerm> boundVars = new LinkedList<VariableTerm>();

    private final TermBuilder tb;

    /**
     * Instantiates a new term translator.
     *
     * If needed, the presented symbol table may be extended!
     *
     * @param symbolTable
     *            non-<code>null</code> symbol table for lookup of symbols.
     */
    public TreeTermTranslator(SymbolTable symbolTable) {
        assert symbolTable != null;
        this.symbolTable = symbolTable;
        this.tb = new TermBuilder(symbolTable);
    }


    /**
     * Builds a let-cascaded term for a tree and a variable map.
     *
     * All assignments in {@code map} are translated to cascading
     * {@link LetTerm}s. The {@code expression} is then embedded into the
     * cascade
     *
     * @param map
     *            the non-<code>null</code> variable assignment
     * @param expression
     *            the expression to be translated
     * @return the term which represents the let-cascade
     * @throws TermBuildException
     *             if terms in the tree are not well-formed.
     */
    public Term build(VariableMap map, DafnyTree expression) throws TermBuildException {
        Term result = build(expression);

        for (Pair<String, DafnyTree> pair : map) {
            result = buildLetExpression(pair.fst, pair.snd, result);
        }

        return result;

    }

    private Term buildLetExpression(String var, DafnyTree assignment, Term result)
            throws TermBuildException {
        DafnyTree errorTree = assignment;
        try {
            switch(assignment.getType()) {
            case DafnyParser.HAVOC:
                String newConst = assignment.getChild(1).getText();
                FunctionSymbol f = symbolTable.getFunctionSymbol(var);
                // SuffixSymbolTable should handle this:
                FunctionSymbol fPrime = symbolTable.getFunctionSymbol(newConst);
                return new LetTerm(f, new ApplTerm(fPrime), result);

            case DafnyParser.ARRAY_UPDATE:
                Term object = build(assignment.getChild(0));
                Term index = build(assignment.getChild(1));
                Term value = build(assignment.getChild(2));
                FunctionSymbol heap = BuiltinSymbols.HEAP;
                ApplTerm heapTerm = new ApplTerm(heap);
                Term store = new ApplTerm(BuiltinSymbols.STORE1, heapTerm, object, index, value);
                return new LetTerm(heap, store, result);

            case DafnyParser.LISTEX:
                // TODO: In a later revision make this seq<?> or similar.
                List<Pair<FunctionSymbol, Term>> updates = new ArrayList<>();
                for (int i = 0; i < assignment.getChildCount(); i++) {
                    f = symbolTable.getFunctionSymbol(var + "_" + i);
                    if (f == null) {
                        f = new FunctionSymbol(var + "_" + i, Sort.INT);
                        symbolTable.addFunctionSymbol(f);
                    }
                    updates.add(new Pair<>(f, build(assignment.getChild(i))));
                }
                return new LetTerm(updates, result);

            default:
                // in this case for error we must take parent of the expression
                errorTree = (DafnyTree) assignment.getParent();
                f = symbolTable.getFunctionSymbol(var);
                value = build(assignment);
                return new LetTerm(f, value, result);
            }
        } catch (TermBuildException ex) {
            if (!ex.hasLocation()) {
                ex.setLocation(errorTree);
            }
            throw ex;
        }
    }

    /**
     * Builds a term for a dafny tree.
     *
     * @param tree the non-<code>null</code> tree object standing for the term
     * @return the term representing the tree
     * @throws TermBuildException if the term is not well-formed
     */
    public Term build(DafnyTree tree) throws TermBuildException {

        switch(tree.getType()) {
        case DafnyParser.AND:
            return buildBinary(BuiltinSymbols.AND, tree);
        case DafnyParser.OR:
            return buildBinary(BuiltinSymbols.OR, tree);
        case DafnyParser.IMPLIES:
            return buildBinary(BuiltinSymbols.IMP, tree);
        case DafnyParser.GE:
            return buildBinary(BuiltinSymbols.GE, tree);
        case DafnyParser.GT:
            return buildBinary(BuiltinSymbols.GT, tree);
        case DafnyParser.LE:
            return buildBinary(BuiltinSymbols.LE, tree);
        case DafnyParser.LT:
            return buildBinary(BuiltinSymbols.LT, tree);
        case DafnyParser.PLUS:
            return buildBinary(BuiltinSymbols.PLUS, tree);
        case DafnyParser.MINUS:
            return buildBinary(BuiltinSymbols.MINUS, tree);
        case DafnyParser.TIMES:
            return buildBinary(BuiltinSymbols.TIMES, tree);
        case DafnyParser.UNION:
            return buildBinary(BuiltinSymbols.UNION, tree);
        case DafnyParser.INTERSECT:
            return buildBinary(BuiltinSymbols.INTERSECT, tree);

        case DafnyParser.NOT:
            return buildUnary(BuiltinSymbols.NEG, tree);

        case DafnyParser.EQ:
            return buildEquality(tree);

        case DafnyParser.NEQ:
            return tb.negate(buildEquality(tree));

        case DafnyParser.ID:
        case DafnyParser.NULL:
        case DafnyParser.INT_LIT:
            return buildIdentifier(tree);

        case DafnyParser.LABEL:

        case DafnyParser.ALL:
            return buildQuantifier(QuantTerm.Quantifier.FORALL, tree);
        case DafnyParser.EX:
            return buildQuantifier(QuantTerm.Quantifier.EXISTS, tree);

        case DafnyParser.LENGTH:
            return buildLength(tree);

        case DafnyParser.ARRAY_ACCESS:
            return buildArrayAccess(tree);

        case DafnyParser.NOETHER_LESS:
            return buildNoetherLess(tree);

        default:
            TermBuildException ex =
                new TermBuildException("Cannot translate term: " + tree.toStringTree());
            ex.setLocation(tree);
            throw ex;
        }

    }

    private Term buildArrayAccess(DafnyTree tree) throws TermBuildException {

        Term arrayTerm = build(tree.getChild(0));
        Sort arraySort = arrayTerm.getSort();
        String arraySortName = arraySort.getName();

        if (!arraySortName.matches("array[0-9]*")) {
            throw new RuntimeException(tree.toStringTree());
        }

        int dimension = 0;
        if (arraySortName.length() > 5) {
            dimension = Integer.parseInt(arraySortName.substring(5));
        }

        FunctionSymbol select = symbolTable.getFunctionSymbol("$select" + dimension);

        if (tree.getChildCount() != dimension + 1) {
            throw new RuntimeException();
        }

        List<Term> args = new ArrayList<>();
        args.add(new ApplTerm(BuiltinSymbols.HEAP));
        args.add(arrayTerm);
        for (int i = 1; i <= dimension; i++) {
            args.add(build(tree.getChild(i)));
        }

        return new ApplTerm(select, args);

    }

    private Term buildLength(DafnyTree tree) throws TermBuildException {
        String functionName = tree.toString();
        String suffix = functionName.substring(6);

        int index = 0;
        if (suffix.length() > 0) {
            index = Integer.parseInt(suffix);
        }

        Term t1 = build(tree.getChild(0));

        FunctionSymbol f = symbolTable.getFunctionSymbol("$len" + index);
        return new ApplTerm(f, Arrays.asList(t1));

    }

    private Term buildEquality(DafnyTree tree) throws TermBuildException {
        if (tree.getChildCount() != 2) {
            throw new RuntimeException();
        }

        Term t1 = build(tree.getChild(0));
        Term t2 = build(tree.getChild(1));

        if (!t1.getSort().equals(t2.getSort())) {
            throw new RuntimeException();
        }

        FunctionSymbol f = symbolTable.getFunctionSymbol("$eq_" + t1.getSort().getName());
        return new ApplTerm(f, Arrays.asList(t1, t2));
    }

    private Term buildIdentifier(DafnyTree tree) throws TermBuildException {
        String name = tree.toString();
        for (VariableTerm var : boundVars) {
            if (var.getName().equals(name)) {
                // found a bound variable in context!
                return var;
            }
        }

        FunctionSymbol fct = symbolTable.getFunctionSymbol(name);
        if (fct == null) {
            throw new TermBuildException("Unknown function symbol: " + name);
        }

        return new ApplTerm(fct);
    }

    private Term buildQuantifier(Quantifier q, DafnyTree tree) throws TermBuildException {
        if (tree.getChildCount() != 3) {
            throw new RuntimeException();
        }

        String var = tree.getChild(0).toString();
        Sort t = buildSort(tree.getChild(1));
        VariableTerm varTerm = new VariableTerm(var, t);

        try {
            boundVars.push(varTerm);
            Term formula = build(tree.getChild(2));
            QuantTerm result = new QuantTerm(q, varTerm, formula);
            return result;
        } finally {
            VariableTerm popped = boundVars.pop();
            assert popped == varTerm;
        }
    }

    // Currently that is still simple since only array<int>, arrayN<int> and set<int>
    // are supported besides int.
    // The name of the node is actually the type already... Will change in future!
    private Sort buildSort(DafnyTree child) {
        return SymbexStateToFormula.treeToType(child);
    }

    private Term buildUnary(FunctionSymbol f, DafnyTree tree) throws TermBuildException {
        if (tree.getChildCount() != 1) {
            throw new RuntimeException("Unexpected argument " + tree.toStringTree());
        }

        Term t1 = build(tree.getChild(0));
        return new ApplTerm(f, Collections.singletonList(t1));
    }

    private Term buildBinary(FunctionSymbol f, DafnyTree tree) throws TermBuildException {
        if (tree.getChildCount() != 2) {
            throw new RuntimeException("Unexpected argument " + tree.toStringTree());
        }

        Term t1 = build(tree.getChild(0));
        Term t2 = build(tree.getChild(1));
        return new ApplTerm(f, Arrays.asList(t1, t2));
    }

    private Term buildNoetherLess(DafnyTree tree) throws TermBuildException {
        // TODO refactor this for seq<?> one day when seqs are available
        DafnyTree lhs = tree.getChild(0);
        DafnyTree rhs = tree.getChild(1);

        assert rhs.getType() == DafnyParser.LISTEX
                && lhs.getType() == DafnyParser.ID :
            "limited support so far we inline the comparison";

        Term result = tb.ff();
        String basevar = lhs.toString();
        Term[] vars = new Term[rhs.getChildCount()];
        Term[] terms = new Term[rhs.getChildCount()];

        for (int i = 0; i < rhs.getChildCount(); i++) {
            FunctionSymbol f = symbolTable.getFunctionSymbol(basevar + "_" + i);
            vars[i] = new ApplTerm(f);
            terms[i] = build(rhs.getChild(i));

            Term cond = tb.tt();
            for (int j = 0; j < i; j++) {
                ApplTerm eq = tb.eq(terms[j], vars[j]);
                cond = tb.and(cond, eq);
            }

            cond = tb.and(cond, tb.lessEqual(tb.zero, terms[i]));
            cond = tb.and(cond, tb.less(terms[i], vars[i]));
            result = tb.or(result, cond);
        }

        return result;
    }

}
