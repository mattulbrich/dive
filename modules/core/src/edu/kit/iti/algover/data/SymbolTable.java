/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.data;

import java.util.Collection;

import edu.kit.iti.algover.term.FunctionSymbol;

/**
 * The symbol table is used to resolve function names to {@link FunctionSymbol} objects.
 *
 * Different implementations are used for builtin symbols, symbols declared in the program
 * and symbols created during proof steps.
 */
public interface SymbolTable {

    /**
     * Gets the function symbol which corresponds to a name
     *
     * @param name
     *            the no-<code>null</code> name of function symbol
     * @return the function symbol, <code>null</code> if no such symbols under
     *         the name exists.
     */
    public FunctionSymbol getFunctionSymbol(String name);

    /**
     * Adds a function symbol to the table.
     *
     * Instead modifying this object by adding a symbol, this gives a fresh
     * SymbolTable object which contains the same elements as this table plus
     * the given symbol.
     *
     * @param symbol
     *            the symbol to add to the table
     * @return the freshly created augmented symbol table
     */
    public SymbolTable addFunctionSymbol(FunctionSymbol symbol);

    /**
     * Get the collection of all function symbols known to this table.
     *
     * @return the a freshly created collection of all symbols
     */
    public Collection<FunctionSymbol> getAllSymbols();

}