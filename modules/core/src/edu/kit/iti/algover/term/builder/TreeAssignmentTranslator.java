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
import edu.kit.iti.algover.util.Pair;

public class TreeAssignmentTranslator {

    private final TreeTermTranslator translator;
    private final SymbolTable symbols;
    private final TermBuilder tb;
    private static final FunctionSymbol HEAP_SYMB = BuiltinSymbols.HEAP;


    public TreeAssignmentTranslator(SymbolTable symbols) {
        this.symbols = symbols;
        this.translator = new TreeTermTranslator(symbols);
        this.tb = new TermBuilder(symbols);
    }

    public ImmutableList<Pair<FunctionSymbol, Term>>
                translateAssignments(ImmutableList<DafnyTree> assignments) throws TermBuildException {
        return assignments.map(this::translateAssignment);
    }

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

    public ImmutableList<Term> translateToSSA(ImmutableList<DafnyTree> assignments, DafnyTree expression) throws TermBuildException {
    throw new Error();
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

        Term appl = tb.storeField(tb.heap(), object, field, assigned);
        return new Pair<>(HEAP_SYMB, appl);
    }

    private Pair<FunctionSymbol,Term> translateSubAccess(DafnyTree receiver, Term assigned) throws TermBuildException {

        String type = receiver.getChild(0).getExpressionType().getText();
        Term subbedItem = translator.build(receiver.getChild(0));

        Term index = translator.build(receiver.getChild(1));
        if (type.equals("array")) {
            Term appl = tb.storeArray(tb.heap(), subbedItem, index, assigned);
            return new Pair<>(HEAP_SYMB, appl);

        } else if (type.equals("seq")) {
            Term appl = tb.seqUpd(subbedItem, index, assigned);
            return translateAssignment(receiver.getChild(0), appl);

            // TODO One day ... map ... other types

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

            Term appl = tb.storeField(tb.heap(), self, field, assigned);
            return new Pair<>(HEAP_SYMB, appl);
        }

        // local variable or parameter ...
        // TODO might be a good place to make sure no parameter is modified
        String name = receiver.getText();
        FunctionSymbol symbol = symbols.getFunctionSymbol(receiver.getText());

        if(symbol == null) {
            throw new TermBuildException("Unknown identifier " + name).setLocation(receiver);
        }

        if(!assigned.getSort().isSubtypeOf(symbol.getResultSort())) {
            throw new TermBuildException("The sorts of the variable and expression do not agree: Assigning " +
                    assigned.getSort() + " to " + symbol.getResultSort());
        }

        return new Pair<>(symbol, assigned);
    }
}
