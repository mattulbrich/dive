/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.boogie;

import edu.kit.iti.algover.dafnystructures.DafnyFunction;
import edu.kit.iti.algover.dafnystructures.DafnyFunctionSymbol;
import edu.kit.iti.algover.dafnystructures.TarjansAlgorithm;
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
import edu.kit.iti.algover.term.builder.ReplacementVisitor;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.builder.TermBuilder;
import edu.kit.iti.algover.term.builder.TreeTermTranslator;
import edu.kit.iti.algover.util.ImmutableLinearSet;
import edu.kit.iti.algover.util.Util;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

/**
 * Requires that {@link edu.kit.iti.algover.dafnystructures.TarjansAlgorithm} has
 * been executed as this adds the infomration about the strongly connected
 * components.
 */
public class BoogieFunctionDefinitionVisitor extends ReplacementVisitor<Void> {

    private Map<DafnyFunctionSymbol, FunctionSymbol> introducedLimitFunctions = new LinkedHashMap<>();
    private Queue<DafnyFunctionSymbol> todo = new LinkedList<>();
    private Set<DafnyFunctionSymbol> done = new HashSet<>();
    private DafnyFunctionSymbol currentSymbol;

    public BoogieFunctionDefinitionVisitor() {
    }

    @Override
    public Term visit(ApplTerm term, Void arg) throws TermBuildException {

        Term visited = super.visit(term, null);

        FunctionSymbol fs = term.getFunctionSymbol();
        if (fs instanceof DafnyFunctionSymbol) {
            DafnyFunctionSymbol dfs = (DafnyFunctionSymbol) fs;
            if(currentSymbol != null && done.contains(dfs) &&
                    getSCC(dfs).equals(getSCC(currentSymbol))) {
                FunctionSymbol replacement = introducedLimitFunctions.get(dfs);
                if (replacement == null) {
                    replacement = new FunctionSymbol(dfs.getName() + "$limited", dfs.getResultSort(), dfs.getArgumentSorts());
                    introducedLimitFunctions.put(dfs, replacement);
                }
                List<Term> subterms = visited != null ? visited.getSubterms() : term.getSubterms();
                return new ApplTerm(replacement, subterms);
            }

            if(!done.contains(dfs) && !todo.contains(dfs)) {
                todo.add(dfs);
            }
        }

        return visited;
    }

    private static String getSCC(DafnyFunctionSymbol dfs) {
        DafnyTree declRef = dfs.getOrigin().getRepresentation().getExpressionType();
        assert declRef.getType() == TarjansAlgorithm.CALLGRAPH_SCC;
        return declRef.toString();
    }


    public void findFunctionDefinitions(SymbolTable symbols, BoogieVisitor visitor) throws TermBuildException {
        Function<Term, Term> oldTrigFunc = visitor.getTriggerFunction();
        while(!todo.isEmpty()) {
            currentSymbol = todo.remove();
            done.add(currentSymbol);
            DafnyFunction function = currentSymbol.getOrigin();
            Term axiom = makeAxiom(currentSymbol, symbols);
            Term equality = stripQuantifiers(axiom);
            visitor.setTriggerFunction(t ->
                    t == equality ? t.getTerm(0) :
                            oldTrigFunc != null ? oldTrigFunc.apply(t) : null);

            visitor.getAxioms().add("axiom " + axiom.accept(visitor, null) + ";");
        }
        visitor.setTriggerFunction(oldTrigFunc);
    }

    private Term stripQuantifiers(Term term) {
        while (term instanceof QuantTerm) {
            term = term.getTerm(0);
        }
        return term;
    }

    /*
     * The result is of the form
     *    f(var0, var1, var2) = ...
     */
    private Term makeAxiom(DafnyFunctionSymbol dfs, SymbolTable symbols) throws TermBuildException {

        DafnyFunction function = dfs.getOrigin();
        TermBuilder tb = new TermBuilder(symbols);
        DafnyTree expression = function.getExpression();
        List<DafnyTree> formalParams = function.getParameters();
        TreeTermTranslator ttt = new TreeTermTranslator(symbols);
        List<VariableTerm> boundVars = new ArrayList<>();

        VariableTerm heapVar = new VariableTerm("heap", Sort.HEAP);
        boundVars.add(heapVar);

        if(function.isDeclaredInClass()) {
            VariableTerm recVar = new VariableTerm("this", dfs.getArgumentSorts().get(1));
            boundVars.add(recVar);
        }

        for (int i = 0; i < formalParams.size(); i++) {
            DafnyTree formalParam = formalParams.get(i);
            String name = formalParam.getFirstChildWithType(DafnyParser.ID).getText();
            VariableTerm var = new VariableTerm(name, dfs.getArgumentSorts().get(1));
            boundVars.add(var);
        }

        boundVars.forEach(ttt::bindVariable);
        ApplTerm app = new ApplTerm(dfs, boundVars);

        Term translation = ttt.build(expression);

        translation = this.collectAndMask(translation);

        translation = tb.eq(app, translation);

        for (VariableTerm var : boundVars) {
            translation = new QuantTerm(Quantifier.FORALL, var, translation);
        }

        return translation;

    }

    public Term collectAndMask(Term term) throws TermBuildException {
        Term result = term.accept(this, null);
        if (result == null) {
            return term;
        } else {
            return result;
        }
    }
}
