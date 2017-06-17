/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;

import org.antlr.runtime.tree.Tree;

import edu.kit.iti.algover.SymbexStateToFormula;
import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.QuantTerm;
import edu.kit.iti.algover.term.QuantTerm.Quantifier;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.util.HistoryMap;
import edu.kit.iti.algover.util.ImmutableList;
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

    /**
     * The Constant HEAP_VAR is the variable used for for heap assignments.
     */
    private static final VariableTerm HEAP_VAR =
            new VariableTerm("heap", Sort.HEAP);

    /**
     * The symbol table from which the function symbols etc are to be taken.
     */
    private final SymbolTable symbolTable;

    /**
     * All bound variables are stored here during parsing.
     *
     * Invariant: Is empty as soon as parsing method returns.
     */
    private final HistoryMap<String, VariableTerm> boundVars =
            new HistoryMap<>(new HashMap<>());

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
     * @param history
     *            the non-<code>null</code> list of observed assignments
     * @param expression
     *            the expression to be translated
     * @return the term which represents the let-cascade
     * @throws TermBuildException
     *             if terms in the tree are not well-formed.
     */
    public Term build(ImmutableList<DafnyTree> history, DafnyTree expression)
            throws TermBuildException {
        return buildLetCascade(history.reverse(), expression);
    }

    private Term buildLetCascade(ImmutableList<DafnyTree> history, DafnyTree expression)
            throws TermBuildException {
        if (history.size() == 0) {
            return build(expression);
        } else {
            return buildLetExpression(history.getHead(),
                    history.getTail(), expression);
        }
    }

    private Term buildLetExpression(DafnyTree assignment, ImmutableList<DafnyTree> tail, DafnyTree result)
            throws TermBuildException {
        DafnyTree errorTree = assignment;

        assert assignment.getType() == DafnyParser.ASSIGN;

        try {
            DafnyTree receiver = assignment.getChild(0);
            DafnyTree expression = assignment.getChild(1);
            LetTerm let;
            switch (receiver.getType()) {
            case DafnyParser.ID:
                DafnyTree ref = receiver.getDeclarationReference();
                if (ref.getType() != DafnyParser.FIELD) {
                    String name = receiver.getText();
                    VariableTerm f = new VariableTerm(name, build(expression).getSort());
                    boundVars.put(name, f);
                    let = new LetTerm(f, build(expression), buildLetCascade(tail, result));
                    boundVars.pop();
                    return let;
                } else {
                    Term self = tb.self();
                    Term field = tb.makeFieldConst(
                            ref.getParent().getChild(0).getText(),
                            ref.getChild(0).getText());
                    Term value = build(expression);
                    FunctionSymbol store =
                            BuiltinSymbols.STORE.instantiate(
                                    Arrays.asList(self.getSort(), value.getSort()));

                    Term appl = new ApplTerm(store, getHeap(), self, field, value);
                    boundVars.put(HEAP_VAR.getName(), HEAP_VAR);
                    let = new LetTerm(HEAP_VAR, appl, buildLetCascade(tail, expression));
                    boundVars.pop();
                    return let;
                }

            case DafnyParser.FIELD_ACCESS: {
                Term object = build(receiver.getChild(0));
                Term field = tb.makeFieldConst(object.getSort().toString(),
                        receiver.getChild(1).getText());
                Term value = build(expression);

                Term appl = tb.storeField(getHeap(), object, field, value);
                boundVars.put(HEAP_VAR.getName(), HEAP_VAR);
                let = new LetTerm(HEAP_VAR, appl, buildLetCascade(tail, expression));
                boundVars.pop();
                return let;
            }

            case DafnyParser.ARRAY_ACCESS: {
                // XXX
                FunctionSymbol store = symbolTable.getFunctionSymbol("$storeArr[int]");
                Term object = build(receiver.getChild(0));
                Term index = build(receiver.getChild(1));
                Term value = build(expression);
                FunctionSymbol heap = BuiltinSymbols.HEAP;
                ApplTerm heapTerm = new ApplTerm(heap);
                Term appl = new ApplTerm(store, heapTerm, object, index, value);
                boundVars.put(HEAP_VAR.getName(), HEAP_VAR);
                let = new LetTerm(HEAP_VAR, appl, buildLetCascade(tail, expression));
                boundVars.pop();
                return let;
            }

            //            case DafnyParser.LISTEX:
            //                // TODO: In a later revision make this seq<?> or similar.
            //                List<Pair<FunctionSymbol, Term>> updates = new ArrayList<>();
            //                for (int i = 0; i < assignment.getChildCount(); i++) {
            //                    f = symbolTable.getFunctionSymbol(var + "_" + i);
            //                    if (f == null) {
            //                        f = new FunctionSymbol(var + "_" + i, Sort.INT);
            //                        symbolTable.addFunctionSymbol(f);
            //                    }
            //                    updates.add(new Pair<>(f, build(assignment.getChild(i))));
            //                }
            //                return new LetTerm(updates, result);

            default:
                throw new Error("Unsupported assignment type: " + receiver.getType());
            }
        } catch (TermBuildException ex) {
            if (!ex.hasLocation()) {
                ex.setLocation(errorTree);
            }
            throw ex;
        }
    }

    private Term getHeap() throws TermBuildException {
        VariableTerm bound = boundVars.get(HEAP_VAR.getName());
        if(bound != null) {
            return bound;
        } else {
            return tb.heap();
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

        switch (tree.getType()) {
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
            // TODO generalize this beyond integer sets
            return buildBinary(symbolTable.getFunctionSymbol("$union[int]"), tree);
        case DafnyParser.INTERSECT:
            // TODO generalize this beyond integer sets
            return buildBinary(symbolTable.getFunctionSymbol("$intersect[int]"), tree);

        case DafnyParser.NOT:
            return buildUnary(BuiltinSymbols.NEG, tree);

        case DafnyParser.EQ:
            return buildEquality(tree);

        case DafnyParser.NEQ:
            return tb.negate(buildEquality(tree));

        case DafnyParser.ID:
        case DafnyParser.TRUE:
        case DafnyParser.FALSE:
        case DafnyParser.INT_LIT:
            return buildIdentifier(tree);

        case DafnyParser.NULL:
            return buildNull(tree);

        case DafnyParser.LABEL:

        case DafnyParser.ALL:
            return buildQuantifier(QuantTerm.Quantifier.FORALL, tree);
        case DafnyParser.EX:
            return buildQuantifier(QuantTerm.Quantifier.EXISTS, tree);

        case DafnyParser.LET:
            return buildLet(tree);

        case DafnyParser.IF:
            return buildIf(tree);

        case DafnyParser.LENGTH:
            return buildLength(tree);

        case DafnyParser.ARRAY_ACCESS:
            return buildArrayAccess(tree);

        case DafnyParser.NOETHER_LESS:
            return buildNoetherLess(tree);

        case DafnyParser.CALL:
            return buildCall(tree);

        default:
            TermBuildException ex =
                new TermBuildException("Cannot translate term: " + tree.toStringTree());
            ex.setLocation(tree);
            throw ex;
        }

    }

    private Term buildIf(DafnyTree tree) throws TermBuildException {

        DafnyTree ifTree = tree.getChild(0);
        DafnyTree thenTree = tree.getChild(1);
        DafnyTree elseTree = tree.getChild(2);

        Term ifCond = build(ifTree);
        Term thenExp = build(thenTree);
        Term elseExp = build(elseTree);

        Sort sort = thenExp.getSort();
        FunctionSymbol ifFct = BuiltinSymbols.ITE.instantiate(Collections.singletonList(sort));

        return new ApplTerm(ifFct, ifCond, thenExp, elseExp);
    }


    private Term buildCall(DafnyTree tree) throws TermBuildException {

        assert tree.getChildCount() == 2
                : "Calls with receivers not yet supported!";

        String id = tree.getChild(0).getText();
        FunctionSymbol fct = symbolTable.getFunctionSymbol(id);
        if (fct == null) {
            throw new TermBuildException("Unknown symbol "
                    + id + ". Remember that method calls not allowed in expressions.");
        }

        List<Term> argTerms = new ArrayList<>();
        for (DafnyTree arg : tree.getChild(1).getChildren()) {
            argTerms.add(build(arg));
        }

        return new ApplTerm(fct, argTerms);
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

    private Term buildNull(DafnyTree tree) throws TermBuildException {
        return tb._null();
    }


    private Term buildEquality(DafnyTree tree) throws TermBuildException {
        assert tree.getChildCount() == 2;

        Term t1 = build(tree.getChild(0));
        Term t2 = build(tree.getChild(1));

        Sort sort = t1.getSort();
        if (Sort.NULL.isSubtypeOf(sort)) {
            sort = Sort.OBJECT;
        }

        FunctionSymbol f = symbolTable.getFunctionSymbol("$eq[" + sort + "]");
        return new ApplTerm(f, Arrays.asList(t1, t2));
    }

    private Term buildIdentifier(DafnyTree tree) throws TermBuildException {
        String name = tree.toString();
        VariableTerm var = boundVars.get(name);
        if (var != null) {
            // found a bound variable in context!
            return var;
        }

        DafnyTree decl = tree.getDeclarationReference();
        if (decl != null && decl.getType() == DafnyParser.FIELD) {
            // if there is a field by that name ...
            Term field = tb.makeFieldConst(decl.getParent().getChild(0).getText(), name);
            Term self = tb.self();
            return tb.selectField(getHeap(), self, field);
        }

        FunctionSymbol fct = symbolTable.getFunctionSymbol(name);
        if (fct == null) {
            throw new TermBuildException("Unknown identifier " + name);
        }

        return new ApplTerm(fct);
    }

    private Term buildQuantifier(Quantifier q, DafnyTree tree) throws TermBuildException {
        assert tree.getChildCount() == 3;

        String var = tree.getChild(0).getText();
        Sort t = buildSort(tree.getChild(1));
        VariableTerm varTerm = new VariableTerm(var, t);

        try {
            boundVars.put(var, varTerm);
            Term formula = build(tree.getChild(2));
            QuantTerm result = new QuantTerm(q, varTerm, formula);
            return result;
        } finally {
            boundVars.rewindHistory(boundVars.size() - 1);
        }
    }

    private Term buildLet(DafnyTree tree) throws TermBuildException {

        List<DafnyTree> targets = tree.getChild(0).getChildren();

        if (targets.size() + 2 != tree.getChildCount()) {
            throw new TermBuildException("Mismatched assignments in let expression: "
                    + targets.size() + " variables, but "
                    + (tree.getChildCount() - 2) + " expressions.");
        }

        List<Pair<VariableTerm, Term>> substs = new ArrayList<>();
        for (int i = 0; i < targets.size(); i++) {
            Term term = build(tree.getChild(i+1));
            VariableTerm var = new VariableTerm(targets.get(i).getText(), term.getSort());
            substs.add(new Pair<>(var, term));
        }

        // only bind them now after all expressions have been parsed
        int rewindPos = boundVars.getHistory();
        try {
            for (Pair<VariableTerm, Term> pair : substs) {
                boundVars.put(pair.fst.getName(), pair.fst);
            }

            Term inner = build(tree.getLastChild());
            LetTerm result = new LetTerm(substs, inner);
            return result;
        } finally {
            boundVars.rewindHistory(rewindPos);
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
        assert tree.getChildCount() == 2 :
            "Unexpected argument " + tree.toStringTree();

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


    /* for testing */
    int countBoundVars() {
        return boundVars.size();
    }

}