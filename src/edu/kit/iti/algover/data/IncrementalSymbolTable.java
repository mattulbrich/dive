/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015 Karlsruhe Institute of Technology
 */

package edu.kit.iti.algover.data;

import java.util.ArrayList;
import java.util.Collection;

import edu.kit.iti.algover.term.FunctionSymbol;

/**
 * This incremental table is used to add one function symbol to the list of
 * available symbols.
 *
 * However, the addition is made in an immutable fashion such that existing maps
 * can be shared by multiple successor nodes.
 *
 * This class should be used by all
 * {@link SymbolTable#addFunctionSymbol(FunctionSymbol)} implementations.
 *
 * @author Mattias Ulbrich
 *
 */
public class IncrementalSymbolTable implements SymbolTable {

    private final FunctionSymbol symb;
    private final SymbolTable parent;

    public IncrementalSymbolTable(SymbolTable parent, FunctionSymbol symb) {
        this.parent = parent;
        this.symb = symb;
    }

    @Override
    public FunctionSymbol getFunctionSymbol(String name) {
        if(name.equals(symb.getName())) {
            return symb;
        } else {
            return parent.getFunctionSymbol(name);
        }
    }

    @Override
    public SymbolTable addFunctionSymbol(FunctionSymbol symb) {
        return new IncrementalSymbolTable(this, symb);
    }

    @Override
    public Collection<FunctionSymbol> getAllSymbols() {
        Collection<FunctionSymbol> result;
        if(parent != null) {
            result = parent.getAllSymbols();
        } else {
            result = new ArrayList<FunctionSymbol>();
        }

        result.add(symb);
        return result;
    }

}