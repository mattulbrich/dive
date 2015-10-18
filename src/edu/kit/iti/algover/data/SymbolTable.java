package edu.kit.iti.algover.data;

import java.util.Collection;

import edu.kit.iti.algover.term.FunctionSymbol;

public interface SymbolTable {

    public FunctionSymbol getFunctionSymbol(String name);

    public SymbolTable addFunctionSymbol(FunctionSymbol symb);

    public Collection<FunctionSymbol> getAllSymbols();

}