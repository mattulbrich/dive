/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.ProgramDatabase;
import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SuffixSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.symbex.AssertionElement;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.builder.TermBuilder;
import edu.kit.iti.algover.term.builder.TreeTermTranslator;

import java.util.ArrayList;
import java.util.Collection;

/**
 * Created by sarah on 8/25/16.
 */
public class SymbexPathToTopFormula {

    private final DafnyTree method;
    private final SymbolTable symbolTable;
    private final TermBuilder termBuilder;
    private final TreeTermTranslator ttt;

    public SymbexPathToTopFormula(DafnyTree method) {
        this.method = method;
        this.symbolTable = makeSymbolTable();
        this.termBuilder = new TermBuilder(symbolTable);
         this.ttt = new TreeTermTranslator(symbolTable);
    }

    private SymbolTable makeSymbolTable() {

        Collection<FunctionSymbol> map = new ArrayList<>();

        for (DafnyTree decl : ProgramDatabase.getAllVariableDeclarations(method)) {
            String name = decl.getChild(0).toString();
            Sort sort = treeToType(decl.getChild(1));
            map.add(new FunctionSymbol(name, sort));
        }

        MapSymbolTable st = new SuffixSymbolTable(new BuiltinSymbols(), map);
        return st;
    }

    // TODO check parameters and stuff
    public static Sort treeToType(DafnyTree tree) {
        String name = tree.toString();
        if("array".equals(name)) {
            name = "array1";
        }

        return new Sort(name);
    }

    public Term fromPO(SymbexPath p, AssertionElement e) throws TermBuildException {
        Term formula = ttt.build(p.getAssignmentHistory(), e.getExpression());
        return formula;
    }


    public Term fromPCE(SymbexPath p, PathConditionElement pce) throws  TermBuildException{
        Term formula = ttt.build(p.getAssignmentHistory(), pce.getExpression());

        return formula;
    }

    public Collection<Term> from(SymbexPath symbexState) throws TermBuildException {

        Collection<Term> result = new ArrayList<>();

        TreeTermTranslator ttt = new TreeTermTranslator(symbolTable);

        for(PathConditionElement pce : symbexState.getPathConditions()) {
            Term formula = ttt.build(pce.getVariableMap(), pce.getExpression());
            result.add(formula);
        }

        assert symbexState.getProofObligations().size() == 1;
        AssertionElement po = symbexState.getProofObligations().getHead();
        DafnyTree expression = po.getExpression();
        Term formula = ttt.build(symbexState.getAssignmentHistory(), expression);
        result.add(termBuilder.negate(formula));

        return result;

    }

    public SymbolTable getSymbolTable() {
        return symbolTable;
    }

}
