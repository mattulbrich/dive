package edu.kit.iti.algover.data;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Map;

import edu.kit.iti.algover.term.FunctionSymbol;

public class MapSymbolTable implements SymbolTable {

    private final Map<String, FunctionSymbol> functionMap;
    private final SymbolTable parentTable;

    public MapSymbolTable(Map<String, FunctionSymbol> map) {
        this(null, map);
    }

    public MapSymbolTable(SymbolTable parentTable, Map<String, FunctionSymbol> functionMap) {
        this.parentTable = parentTable;
        this.functionMap = functionMap;
    }

    /* (non-Javadoc)
     * @see edu.kit.iti.algover.data.SymbolTable#getFunctionSymbol(java.lang.String)
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

        if(result == null) {
            throw new RuntimeException("The function symbol " + name + " cannot be found");
        }

        return result;
    }

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
        result = new ArrayList<FunctionSymbol>();
        result.addAll(functionMap.values());
        return result;
    }

}
