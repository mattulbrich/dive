/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.data;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import edu.kit.iti.algover.term.FunctionSymbol;

/**
 * This symbol table is based upon a lookup table for symbols by their names.
 *
 * It is an invariant that all function symbols are filed under their name.
 *
 * The map should not be altered after creation other than by a
 * {@link #resolve(String)} reimplementation.
 *
 * @author Mattias Ulbrich
 */
public class MapSymbolTable implements SymbolTable {

    /**
     * The non-null map in which the symbols are stored.
     */
    private final Map<String, FunctionSymbol> functionMap;

    /**
     * The optional parent table to defer unresolved calls to.
     */
    private final SymbolTable parentTable;

    /**
     * Instantiates a new map symbol table.
     *
     * @param symbols
     *            a non-null collection of function symbols
     */
    public MapSymbolTable(Collection<FunctionSymbol> symbols) {
        this(null, symbols);
    }

    /**
     * Instantiates a new map symbol table.
     *
     * @param parentTable
     *            the parent symbol table, may be <code>null</code>
     * @param symbols
     *            a non-<code>null</code> collection of function symbols
     */
    public MapSymbolTable(SymbolTable parentTable, Collection<FunctionSymbol> symbols) {
        this.parentTable = parentTable;
        this.functionMap = toMap(symbols);
    }

    /*
     * turns a collection into a map (by their names)
     */
    private static Map<String, FunctionSymbol> toMap(Collection<FunctionSymbol> symbols) {
        Map<String, FunctionSymbol> result = new HashMap<>();
        for (FunctionSymbol fs : symbols) {
            result.put(fs.getName(), fs);
        }
        return result;
    }

    /**
     * Look up a function symbol in the function map.
     *
     * If not found, then call {@link #resolve(String)} to create symbols on
     * demand. If still not found, then defer the lookup to the parent symbol
     * table.
     */
    @Override
    public FunctionSymbol getFunctionSymbol(String name) {

        FunctionSymbol result = functionMap.get(name);

        if(result == null) {
            result = resolve(name);
            if(result != null) {
                functionMap.put(name, result);
            }
        }

        if(result == null && parentTable != null) {
            result = parentTable.getFunctionSymbol(name);
        }

        return result;
    }

    /**
     * Resolve a name for which no symbol is in the table.
     *
     * By default this returns <code>null</code>.
     *
     * @param name
     *            the name to lookup
     * @return the function symbol created for the name, <code>null</code> if
     *         this cannot be resolved.
     */
    protected FunctionSymbol resolve(String name) {
        return null;
    }

    @Override
    public SymbolTable addFunctionSymbol(FunctionSymbol symb) {
        return new IncrementalSymbolTable(this, symb);
    }

    @Override
    public Collection<FunctionSymbol> getAllSymbols() {
        Collection<FunctionSymbol> result;
        if(parentTable != null) {
            result = parentTable.getAllSymbols();
        } else {
            result = new ArrayList<FunctionSymbol>();
        }

        result.addAll(functionMap.values());

        return result;
    }
}
