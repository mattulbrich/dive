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
import nonnull.NonNull;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Queue;
import java.util.Set;
import java.util.function.Function;

/**
 * This class can be used to visit terms. It then identifies called functions
 * inside. If it encounters a not yet observed function it adds it to a to-do
 * list. If it encounters an already observed function in the same strongly
 * connected call component, it replaces it by a "$limited" derivate.
 *
 * Axioms for all encountered functions are added, their definitions are
 * visited as well to obtain a more precise translation.
 *
 * Requires that {@link edu.kit.iti.algover.dafnystructures.TarjansAlgorithm} has
 * been executed as this adds the information about the strongly connected
 * components.
 *
 * @author mattias ulbrich
 */
public class BoogieFunctionDefinitionVisitor extends ReplacementVisitor<Void> {

    /**
     * collection of already introduced $limited variants.
     */
    private Map<DafnyFunctionSymbol, FunctionSymbol> introducedLimitFunctions =
            new LinkedHashMap<>();

    /**
     * encountered symbols that should be axiomatised
     */
    private Queue<DafnyFunctionSymbol> todo = new LinkedList<>();

    /**
     * encountered symbols that have already been axiomatised
     */
    private Set<DafnyFunctionSymbol> done = new HashSet<>();

    /**
     * the symbol in whose definition we currently are.
     */
    private DafnyFunctionSymbol currentSymbol;

    @Override
    public Term visit(ApplTerm term, Void arg) throws TermBuildException {

        Term visited = super.visit(term, null);

        FunctionSymbol fs = term.getFunctionSymbol();
        if (fs instanceof DafnyFunctionSymbol) {
            DafnyFunctionSymbol dfs = (DafnyFunctionSymbol) fs;
            if(currentSymbol != null && done.contains(dfs) &&
                    getSCC(dfs).equals(getSCC(currentSymbol))) {

                // Interesting case: symbol already seen and in same scc -->
                // replace by $limited version.

                FunctionSymbol replacement = introducedLimitFunctions.get(dfs);
                if (replacement == null) {
                    replacement = new FunctionSymbol(dfs.getName() + "$limited",
                            dfs.getResultSort(), dfs.getArgumentSorts());
                    introducedLimitFunctions.put(dfs, replacement);
                }
                List<Term> subterms =
                        visited != null ? visited.getSubterms() : term.getSubterms();
                return new ApplTerm(replacement, subterms);
            }

            if(!done.contains(dfs) && !todo.contains(dfs)) {
                todo.add(dfs);
            }
        }

        return visited;
    }

    /*
     * read the SCC from the place where TarjansAlgorithm has put it.
     */
    private static String getSCC(DafnyFunctionSymbol dfs) {
        DafnyTree declRef = dfs.getOrigin().getRepresentation().getExpressionType();
        assert declRef.getType() == TarjansAlgorithm.CALLGRAPH_SCC;
        return declRef.toString();
    }

    /**
     * Iterates over the function symbols collected during earlier visitations.
     *
     * Adds according axioms to the axiom set of {@code visitor}.
     *
     * The definitions are themselves visited possible adding further symbols
     * to the collection.
     *
     * @param symbols the table to take symbols from, not changed.
     * @param visitor used for producing and stoprin axioms.
     * @throws TermBuildException
     */
    public void findFunctionDefinitions(@NonNull SymbolTable symbols, @NonNull BoogieVisitor visitor) throws TermBuildException {
        Function<Term, Term> oldTrigFunc = visitor.getTriggerFunction();
        while(!todo.isEmpty()) {
            currentSymbol = todo.remove();
            done.add(currentSymbol);
            Term axiom = makeAxiom(currentSymbol, symbols);
            Term equality = stripQuantifiers(axiom);
            visitor.setTriggerFunction(t ->
                    t == equality ? t.getTerm(0) :
                            oldTrigFunc != null ? oldTrigFunc.apply(t) : null);

            visitor.getAxioms().add("axiom " + axiom.accept(visitor, null) + ";");
        }
        visitor.setTriggerFunction(oldTrigFunc);

        addLimitationAxioms(visitor, symbols);

    }

    /*
     * Add axioms for the limited functions of the form
     *    forall ... :: { f(x) } f(x) = f$limit(x)
     * to make the symbols "more the same".
     */
    private void addLimitationAxioms(BoogieVisitor visitor, SymbolTable symbols) throws TermBuildException {
        Function<Term, Term> oldTrigFunc = visitor.getTriggerFunction();
        for (Entry<DafnyFunctionSymbol, FunctionSymbol> en : introducedLimitFunctions.entrySet()) {
            FunctionSymbol f1 = en.getKey();
            FunctionSymbol f2 = en.getValue();
            Term axiom;
            axiom = makeLimitAxiom(f1, f2, symbols);
            Term equality = stripQuantifiers(axiom);
            visitor.setTriggerFunction(t ->
                    t == equality ? t.getTerm(0) :
                            oldTrigFunc != null ? oldTrigFunc.apply(t) : null);
            visitor.getAxioms().add("axiom " + axiom.accept(visitor, null) + ";");
        }
        visitor.setTriggerFunction(oldTrigFunc);
    }

    /*
     * make forall ... :: f1(x) = f2(x)
     */
    private Term makeLimitAxiom(FunctionSymbol f1, FunctionSymbol f2, SymbolTable symbols) throws TermBuildException {
        TermBuilder tb = new TermBuilder(symbols);
        List<VariableTerm> boundVars = new ArrayList<>();
        int i = 0;
        for (Sort argumentSort : f1.getArgumentSorts()) {
            boundVars.add(new VariableTerm("v" + i, argumentSort));
            i++;
        }
        ApplTerm appl1 = new ApplTerm(f1, boundVars);
        ApplTerm appl2 = new ApplTerm(f2, boundVars);
        Term result = tb.eq(appl1, appl2);
        for (VariableTerm boundVar : boundVars) {
            result = tb.forall(boundVar, result);
        }
        return result;
    }

    /*
     * get the innermost matrix of possibly nested quantifiers.
     */
    private Term stripQuantifiers(Term term) {
        while (term instanceof QuantTerm) {
            term = term.getTerm(0);
        }
        return term;
    }

    /*
     * The result is of the form
     *      forall var0. forall var1. forall var2. f(var0, var1, var2) = term
     *
     * term is visited as well.
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
            translation = tb.forall(var, translation);
        }

        return translation;

    }

    /**
     * Visit the argument term.
     *
     * Unlike the visitor methods of this class, this version does not return
     * null of no changes have occurred but the original term.
     *
     * @param term term to visit
     * @return visited version, possibly with some function invocations replaced
     * by limited versions, not null
     * @throws TermBuildException if construction fails.
     */
    public Term collectAndMask(Term term) throws TermBuildException {
        Term result = term.accept(this, null);
        if (result == null) {
            return term;
        } else {
            return result;
        }
    }
}
