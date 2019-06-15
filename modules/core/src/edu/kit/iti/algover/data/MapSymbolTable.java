/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.data;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.FunctionSymbolFamily;
import edu.kit.iti.algover.term.Sort;
import nonnull.DeepNonNull;
import nonnull.NonNull;
import nonnull.Nullable;

/**
 * This symbol table is based upon a lookup table for symbols by their names.
 *
 * It is an invariant that all function symbols are filed under their name.
 *
 * The map should not be altered after creation other than by a
 * {@link #resolve(String, List<Sort>)} reimplementation.
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

    @Override
    public FunctionSymbol getFunctionSymbol(String name) {
        return getFunctionSymbol(name, Collections.emptyList());
    }

    /*
     * Look up a function symbol in the function map.
     *
     * If not found, then call {@link #resolve(String, List<Sort>)} to create
     * symbols on demand. If still not found, then defer the lookup to the
     * parent symbol table.
     */
    @Override
    public @Nullable FunctionSymbol getFunctionSymbol(@NonNull String name, @DeepNonNull List<Sort> argumentSorts) {
        String lookup = name + FunctionSymbolFamily.toString(argumentSorts);
        FunctionSymbol result = functionMap.get(lookup);

        if(result == null) {
            result = resolve(name, argumentSorts);
            if(result != null) {
                functionMap.put(lookup, result);
            }
        }

        if(result == null && parentTable != null) {
            result = parentTable.getFunctionSymbol(name, argumentSorts);
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
    protected FunctionSymbol resolve(String name, List<Sort> argSorts) {
        return null;
    }

    @Override
    public SymbolTable addFunctionSymbol(FunctionSymbol symb) {
        String name = symb.getName();
        if(functionMap.containsKey(name)) {
            throw new RuntimeException("Symbol name already present: " + name);
        }
        if(parentTable != null && parentTable.getFunctionSymbol(name) != null) {
            throw new RuntimeException("Symbol name already present: " + name);
        }
        functionMap.put(name, symb);
        return this;
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
