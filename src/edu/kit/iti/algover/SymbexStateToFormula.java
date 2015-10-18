/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover;

import java.util.ArrayList;
import java.util.Collection;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.SymbexState;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuilder;
import edu.kit.iti.algover.term.builder.TreeTermTranslator;

// THIS IS A TEMPORARY CLASS ...

public class SymbexStateToFormula {

    private final DafnyTree method;
    private final SymbolTable symbolTable;

    public SymbexStateToFormula(DafnyTree method) {
        this.method = method;
        this.symbolTable = makeSymbolTable();
    }

    private SymbolTable makeSymbolTable() {

        Collection<FunctionSymbol> map = new ArrayList<>();

        for (DafnyTree decl : ProgramDatabase.getAllVariableDeclarations(method)) {
            String name = decl.getChild(0).toString();
            Sort sort = treeToType(decl.getChild(1));
            map.add(new FunctionSymbol(name, sort));
        }

        MapSymbolTable st = new MapSymbolTable(new BuiltinSymbols(), map);
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

    public Collection<Term> from(SymbexState symbexState) {

        Collection<Term> result = new ArrayList<>();

        TreeTermTranslator ttt = new TreeTermTranslator(symbolTable);

        for(PathConditionElement pce : symbexState.getPathConditions()) {
            Term formula = ttt.build(pce.getExpression());
            result.add(formula);
        }

        for(DafnyTree po : symbexState.getProofObligations()) {
            Term formula = ttt.build(po.getLastChild());
            result.add(TermBuilder.negate(formula));
        }

        return result;

    }

    public SymbolTable getSymbolTable() {
        return symbolTable;
    }

}
