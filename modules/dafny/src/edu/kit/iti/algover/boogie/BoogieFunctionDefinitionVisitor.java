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

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;

/**
 * Requires that {@link edu.kit.iti.algover.dafnystructures.TarjansAlgorithm} has
 * been executed as this adds the infomration about the strongly connected
 * components.
 */
public class BoogieFunctionDefinitionVisitor extends ReplacementVisitor<Void> {

    private Map<DafnyFunctionSymbol, FunctionSymbol> introducedLimitFunctions = new IdentityHashMap<>();
    private Map<DafnyFunctionSymbol, Term> axioms = new IdentityHashMap<>();
    private Queue<DafnyFunctionSymbol> todo = new LinkedList<>();
    private DafnyFunctionSymbol currentSymbol;

    public BoogieFunctionDefinitionVisitor() {
    }

    @Override
    public Term visit(ApplTerm term, Void arg) throws TermBuildException {

        Term visited = super.visit(term, null);

        FunctionSymbol fs = term.getFunctionSymbol();
        if (fs instanceof DafnyFunctionSymbol) {
            DafnyFunctionSymbol dfs = (DafnyFunctionSymbol) fs;
            if(currentSymbol != null && axioms.containsKey(dfs) &&
                    getSCC(dfs).equals(getSCC(currentSymbol))) {
                FunctionSymbol replacement = introducedLimitFunctions.get(dfs);
                if (replacement == null) {
                    replacement = new FunctionSymbol(dfs.getName() + "$$limited", dfs.getResultSort(), dfs.getArgumentSorts());
                    introducedLimitFunctions.put(dfs, replacement);
                }
                List<Term> subterms = visited != null ? visited.getSubterms() : term.getSubterms();
                return new ApplTerm(replacement, subterms);
            }

            if(!axioms.containsKey(dfs) && !todo.contains(dfs)) {
                todo.add(dfs);
            }
        }

        return visited;
    }

    private static String getSCC(DafnyFunctionSymbol dfs) {
        DafnyTree declRef = dfs.getOrigin().getRepresentation().getDeclarationReference();
        assert declRef.getType() == TarjansAlgorithm.CALLGRAPH_SCC;
        return declRef.toString();
    }


    public void findFunctionDefinitions(SymbolTable symbols) throws TermBuildException {
        while(!todo.isEmpty()) {
            currentSymbol = todo.remove();
            DafnyFunction function = currentSymbol.getOrigin();
            Term axiom = makeAxiom(currentSymbol, symbols);
            axioms.put(currentSymbol, axiom);
        }
    }

    public void getFunctionDefinitions(BoogieVisitor visitor) {
        for (Term axiom : axioms.values()) {
            visitor.getAxioms().add(axiom.accept(visitor, null));
        }
    }

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
            VariableTerm recVar = new VariableTerm("this", dfs.getArgumentSorts().get(0));
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
