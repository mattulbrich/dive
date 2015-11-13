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
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.QuantTerm;
import edu.kit.iti.algover.term.QuantTerm.Quantifier;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.VariableTerm;

public class TreeTermTranslator {

    private final SymbolTable symbolTable;

    private final Deque<VariableTerm> boundVars = new LinkedList<VariableTerm>();

    public TreeTermTranslator(SymbolTable symbolTable) {
        assert symbolTable != null;
        this.symbolTable = symbolTable;
    }

    public Term build(DafnyTree tree) {

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

        case DafnyParser.ID:

        case DafnyParser.LIT:
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

        default: throw new RuntimeException(tree.toStringTree());
        }

    }

    private Term buildArrayAccess(DafnyTree tree) {

        Term arrayTerm = build(tree.getChild(0));
        Sort arraySort = arrayTerm.getSort();
        String arraySortName = arraySort.getName();

        if(!arraySortName.matches("array[0-9]*")) {
            throw new RuntimeException(tree.toStringTree());
        }

        int dimension = 0;
        if(arraySortName.length() > 5) {
            dimension = Integer.parseInt(arraySortName.substring(5));
        }

        FunctionSymbol select = symbolTable.getFunctionSymbol("$select" + dimension);

        if(tree.getChildCount() != dimension + 1) {
            throw new RuntimeException();
        }

        List<Term> args = new ArrayList<>();
        args.add(arrayTerm);
        for(int i = 1; i <= dimension; i++) {
            args.add(build(tree.getChild(i)));
        }

        return new ApplTerm(select, args);

    }

    private Term buildLength(DafnyTree tree) {
        String functionName = tree.toString();
        String suffix = functionName.substring(6);

        int index = 0;
        if(suffix.length() > 0) {
            index = Integer.parseInt(suffix);
        }

        Term t1 = build(tree.getChild(0));

        FunctionSymbol f = symbolTable.getFunctionSymbol("$len" + index);
        return new ApplTerm(f, Arrays.asList(t1));

    }

    private Term buildEquality(DafnyTree tree) {
        if(tree.getChildCount() != 2) {
            throw new RuntimeException();
        }

        Term t1 = build(tree.getChild(0));
        Term t2 = build(tree.getChild(1));

        if(!t1.getSort().equals(t2.getSort())) {
            throw new RuntimeException();
        }

        FunctionSymbol f = symbolTable.getFunctionSymbol("$eq_" + t1.getSort().getName());
        return new ApplTerm(f, Arrays.asList(t1, t2));
    }

    private Term buildIdentifier(DafnyTree tree) {
        String name = tree.toString();
        for (VariableTerm var : boundVars) {
            if(var.getName().equals(name)) {
                // found a bound variable in context!
                return var;
            }
        }

        FunctionSymbol fct = symbolTable.getFunctionSymbol(name);
        if(fct == null) {
            throw new RuntimeException("Unknown function symbol: " + name);
            // throw new DafnyException("Unknown function symbol: " + name, tree);
        }


        return new ApplTerm(fct);
    }

    private Term buildQuantifier(Quantifier q, DafnyTree tree) {
        if(tree.getChildCount() != 3) {
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

    private Term buildUnary(FunctionSymbol f, DafnyTree tree) {
        if(tree.getChildCount() != 1) {
            throw new RuntimeException("Unexpected argument " + tree.toStringTree());
        }

        Term t1 = build(tree.getChild(0));
        return new ApplTerm(f, Collections.singletonList(t1));
    }

    private Term buildBinary(FunctionSymbol f, DafnyTree tree) {
        if(tree.getChildCount() != 2) {
            throw new RuntimeException("Unexpected argument " + tree.toStringTree());
        }

        Term t1 = build(tree.getChild(0));
        Term t2 = build(tree.getChild(1));
        return new ApplTerm(f, Arrays.asList(t1, t2));
    }

}
