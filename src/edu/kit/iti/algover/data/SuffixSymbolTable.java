/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.data;

import java.util.Collection;

import edu.kit.iti.algover.term.FunctionSymbol;

public class SuffixSymbolTable extends MapSymbolTable {

    public SuffixSymbolTable(Collection<FunctionSymbol> symbols) {
        super(symbols);
    }

    public SuffixSymbolTable(SymbolTable parentTable, Collection<FunctionSymbol> symbols) {
        super(parentTable, symbols);
    }

    @Override
    protected FunctionSymbol resolve(String name) {
        int hash = name.indexOf('#');
        if(hash >= 0) {
            String orgName = name.substring(0, hash);
            FunctionSymbol fs = getFunctionSymbol(orgName);
            if(fs != null) {
                return new FunctionSymbol(name, fs.getResultSort(), fs.getArgumentSorts());
            }
        }
        return null;
    }

}
