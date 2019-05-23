/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.data;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.FunctionSymbolFamily;
import edu.kit.iti.algover.term.Sort;
import nonnull.DeepNonNull;
import nonnull.NonNull;
import nonnull.Nullable;

/**
 * The symbol table is used to resolve function names to {@link FunctionSymbol}
 * objects.
 *
 * Different implementations are used for builtin symbols, symbols declared in
 * the program and symbols created during proof steps.
 */
public interface SymbolTable {

    /**
     * Gets the function symbol which corresponds to a name, instantiated with
     * a list of sort arguments.
     *
     * @param name
     *            the no-<code>null</code> name of function symbol
     * @param argumentSorts
     *            the arguments to apply for an instantiation, may be empty.
     * @return the function symbol, <code>null</code> if no such symbols under
     *         the name exists.
     */
    @Nullable FunctionSymbol getFunctionSymbol(@NonNull String name, @DeepNonNull  List<Sort> argumentSorts);

    /**
     * Gets the function symbol which corresponds to a name.
     *
     * @param name
     *            the no-<code>null</code> name of function symbol
     * @return the function symbol, <code>null</code> if no such symbols under
     *         the name exists.
     */
    default @Nullable FunctionSymbol getFunctionSymbol(@NonNull String name) {
        return getFunctionSymbol(name, Collections.emptyList());
    }


    /**
     * Gets the instantiation of a symbol family.
     *
     * Calling this is favoured over calling {@link FunctionSymbolFamily#instantiate(Sort...)}
     * since this registers the symbol with the table.
     *
     * @param family        The symbol family to instantiate
     * @param argumentSorts the arguments to apply for an instantiation, may be
     *                      empty.
     * @return the function symbol, <code>null</code> if no such symbols under
     * the name exists.
     */
    default @Nullable FunctionSymbol getFunctionSymbol(
            @NonNull FunctionSymbolFamily family, Sort... argumentSorts) {
        return getFunctionSymbol(family.getBaseName(), Arrays.asList(argumentSorts));
    }

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
    SymbolTable addFunctionSymbol(FunctionSymbol symbol);

    /**
     * Get the collection of all function symbols known to this table.
     *
     * @return the a freshly created collection of all symbols
     */
    Collection<FunctionSymbol> getAllSymbols();

}