/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.term.builder;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Immutables;
import edu.kit.iti.algover.util.Pair;
import nonnull.NonNull;

import java.util.Map;

/**
 * The Class TreeAssignmentTranslator is used to create a {@link Term}
 * object from a {@link DafnyTree} together with an assignment history.
 * The latter is represented by a list of DafnyTrees.
 *
 * For the translation of individual expressions, a {@link TreeTermTranslator}
 * is used.
 *
 * @see Term
 * @see DafnyTree
 * @see TreeTermTranslator
 *
 * @author Mattias Ulbrich
 */
public class TreeAssignmentTranslator {

    /**
     * The translator used for the translation of expressions
     */
    private final TreeTermTranslator translator;

    /**
     * The symbol table for lookup. Can be extended during translation!
     */
    private final SymbolTable symbols;

    /**
     * bound to {@link #symbols}, used to create expressions.
     */
    private final TermBuilder tb;

    /**
     * Reference for convenience
     */
    private static final FunctionSymbol HEAP_SYMB = BuiltinSymbols.HEAP;

    /**
     * Create a fresh translator.
     *
     * @param symbols the symbol table for lookup
     */
    public TreeAssignmentTranslator(@NonNull SymbolTable symbols) {
        this.symbols = symbols;
        this.translator = new TreeTermTranslator(symbols);
        this.tb = new TermBuilder(symbols);
    }

    public ImmutableList<Pair<FunctionSymbol, Term>>
                translateAssignments(ImmutableList<DafnyTree> assignments) throws TermBuildException {
        return assignments.map(this::translateAssignment);
    }

    /**
     * Builds a let-cascaded term for a tree and a variable map.
     *
     * All assignments in {@code map} are translated to cascading
     * {@link LetTerm}s. The {@code expression} is then embedded into the
     * cascade
     *
     * @param assignments
     *            the non-<code>null</code> list of observed assignments
     * @param expression
     *            the expression to be translated
     * @return the term which represents the let-cascade
     * @throws TermBuildException
     *             if terms in the tree are not well-formed.
     */
    public Term translateToLet(ImmutableList<DafnyTree> assignments, DafnyTree expression) throws TermBuildException {
        return translateToLet0(assignments.reverse(), expression);
    }

    private Term translateToLet0(ImmutableList<DafnyTree> assignments, DafnyTree expression) throws TermBuildException {

        if(assignments.isEmpty()) {
            return translator.build(expression);
        }

        DafnyTree ass = assignments.getLast();
        Pair<FunctionSymbol, Term> assPair = translateAssignment(ass);
        VariableTerm var = new VariableTerm(assPair.fst.getName(), assPair.fst.getResultSort());
        Term expr = assPair.snd;
        translator.bindVariable(var);
        Term inner = translateToLet0(assignments.getTail(), expression);
        translator.unbindVariable(var);

        return new LetTerm(var, expr, inner);
    }

    public ImmutableList<Pair<FunctionSymbol, Term>> translateToLinear(ImmutableList<DafnyTree> assignments) throws TermBuildException {
        ImmutableList<Pair<FunctionSymbol, Term>> result = ImmutableList.nil();
        for (DafnyTree ass : assignments.reverse()) {
            result = result.append(translateAssignment(ass));
        }
        return result;
    }

    private Pair<FunctionSymbol, Term> translateAssignment(DafnyTree tree) throws TermBuildException {
        assert tree.getType() == DafnyParser.ASSIGN;

        DafnyTree receiver = tree.getChild(0);
        DafnyTree value = tree.getChild(1);
        Term term = translator.build(value);

        try {
            return translateAssignment(receiver, term);
        } catch (TermBuildException e) {
            throw e.setLocationIfUnset(tree);
        }
    }

    private Pair<FunctionSymbol, Term> translateAssignment(DafnyTree receiver, Term term) throws TermBuildException {
        switch(receiver.getType()) {
        case DafnyParser.ID:
            return translateID(receiver, term);
        case DafnyParser.ARRAY_ACCESS:
            return translateSubAccess(receiver, term);
        case DafnyParser.FIELD_ACCESS:
            return translateFieldAccess(receiver, term);
        default:
            throw new TermBuildException("Cannot resolve this assignment target").setLocation(receiver);
        }
    }

    private Pair<FunctionSymbol,Term> translateFieldAccess(DafnyTree receiver, Term assigned) throws TermBuildException {
        Term object = translator.build(receiver.getChild(0));
        DafnyTree ref = receiver.getChild(1).getDeclarationReference();

        Term field = tb.makeFieldConst(
                ref.getParent().getChild(0).getText(), // classname
                ref.getChild(0).getText()); // fieldname

        Term appl = tb.storeField(translator.getHeap(), object, field, assigned);
        return new Pair<>(HEAP_SYMB, appl);
    }

    private Pair<FunctionSymbol,Term> translateSubAccess(DafnyTree receiver, Term assigned) throws TermBuildException {

        String type = receiver.getChild(0).getExpressionType().getText();
        Term subbedItem = translator.build(receiver.getChild(0));

        Term index = translator.build(receiver.getChild(1));
        if (type.equals("array")) {
            Term appl = tb.storeArray(translator.getHeap(), subbedItem, index, assigned);
            return new Pair<>(HEAP_SYMB, appl);

        } else if (type.equals("seq")) {
            Term appl = tb.seqUpd(subbedItem, index, assigned);
            return translateAssignment(receiver.getChild(0), appl);

            // TODO One day ... map ... other types

        } else if (type.equals("array2")) {
            Term index2 = translator.build(receiver.getChild(2));
            Term appl = tb.storeArray2(translator.getHeap(), subbedItem, index, index2, assigned);
            return new Pair<>(HEAP_SYMB, appl);

        } else {
            throw new TermBuildException("Unsupported type for sub access: " +
                    subbedItem.getSort() + " (" + type + ")").setLocation(receiver);
        }
    }


    private Pair<FunctionSymbol, Term> translateID(DafnyTree receiver, Term assigned) throws TermBuildException {
        DafnyTree ref = receiver.getDeclarationReference();
        if (ref.getType() == DafnyParser.FIELD) {
            Term self = tb.self();
            Term field = tb.makeFieldConst(
                    ref.getParent().getChild(0).getText(), // classname
                    ref.getChild(0).getText()); // fieldname

            Term appl = tb.storeField(translator.getHeap(), self, field, assigned);
            return new Pair<>(HEAP_SYMB, appl);
        }

        // local variable or parameter ...
        // TODO might be a good place to make sure no parameter is modified
        String name = receiver.getText();
        FunctionSymbol symbol = symbols.getFunctionSymbol(receiver.getText());

        if(symbol == null) {
            // There is no defined symbol there, so create an artificial one.
            // This is the case, e.g., for $decr or $decr_1, ...
            symbol = new FunctionSymbol(receiver.getText(), assigned.getSort());
            symbols.addFunctionSymbol(symbol);
        }

        if(!assigned.getSort().isSubtypeOf(symbol.getResultSort())) {
            throw new TermBuildException("The sorts of the variable and " +
                    "expression do not agree: Assigning a value of type " +
                    assigned.getSort() + " to an entity of type " +
                    symbol.getResultSort());
        }

        return new Pair<>(symbol, assigned);
    }

    /**
     * Retrieves a map which assigns to every term the {@link DafnyTree} origin.
     *
     * The instance is taken from the internal {@link TreeTermTranslator}
     * instance.
     *
     * Caution! This map is an identity map which maps to every term OBJECT
     * IDENTITY. Two terms which are semantically and structurally equal may
     * have different origins!
     *
     * @return the reference map
     */
    public @NonNull Map<Term,DafnyTree> getReferenceMap() {
        return translator.getReferenceMap();
    }
}
