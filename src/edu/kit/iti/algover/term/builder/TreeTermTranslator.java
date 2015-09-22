package edu.kit.iti.algover.term.builder;

import java.util.Arrays;
import java.util.Deque;
import java.util.LinkedList;

import edu.kit.iti.algover.data.SymbolTable;
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
            return buildBinary(TermBuilder.AND, tree);
        case DafnyParser.OR:
            return buildBinary(TermBuilder.OR, tree);
        case DafnyParser.IMPLIES:
            return buildBinary(TermBuilder.IMP, tree);
        case DafnyParser.GE:
            return buildBinary(TermBuilder.GE, tree);
        case DafnyParser.GT:
            return buildBinary(TermBuilder.GT, tree);
        case DafnyParser.LE:
            return buildBinary(TermBuilder.LE, tree);
        case DafnyParser.LT:
            return buildBinary(TermBuilder.LT, tree);
        case DafnyParser.PLUS:
            return buildBinary(TermBuilder.PLUS, tree);
        case DafnyParser.TIMES:
            return buildBinary(TermBuilder.TIMES, tree);
        case DafnyParser.UNION:
            return buildBinary(TermBuilder.UNION, tree);
        case DafnyParser.INTERSECT:
            return buildBinary(TermBuilder.INTERSECT, tree);

        case DafnyParser.EQ:
            return buildEquality(tree);

        case DafnyParser.ID:
            return buildIdentifier(tree);
        case DafnyParser.LIT:
            return buildBinary(TermBuilder.IMP, tree);

        case DafnyParser.ALL:
            return buildQuantifier(QuantTerm.Quantifier.FORALL, tree);
        case DafnyParser.EX:
            return buildQuantifier(QuantTerm.Quantifier.EXISTS, tree);

        default: throw new RuntimeException(tree.toStringTree());
        }

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
        return new ApplTerm(fct);
    }

    private Term buildQuantifier(Quantifier q, DafnyTree tree) {
        if(tree.getChildCount() != 3) {
            throw new RuntimeException();
        }

        String var = tree.getChild(0).toString();
        Sort t = buildSort(tree.getChild(1));
        Term formula = build(tree.getChild(2));
        VariableTerm varTerm = new VariableTerm(var, t);

        try {
            boundVars.push(varTerm);
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
        String name = child.toString();
        return new Sort(name);
    }

    private Term buildBinary(FunctionSymbol f, DafnyTree tree) {
        if(tree.getChildCount() != 2) {
            throw new RuntimeException();
        }

        Term t1 = build(tree.getChild(0));
        Term t2 = build(tree.getChild(1));
        return new ApplTerm(f, Arrays.asList(t1, t2));
    }

}
