package edu.kit.iti.algover.data;

import java.util.Arrays;
import java.util.Map;

import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;

public class MapSymbolTable implements SymbolTable {

    private final Map<String, FunctionSymbol> functionMap;

    public MapSymbolTable(Map<String, FunctionSymbol> map) {
        this.functionMap = map;
    }

    /* (non-Javadoc)
     * @see edu.kit.iti.algover.data.SymbolTable#getFunctionSymbol(java.lang.String)
     */
    @Override
    public FunctionSymbol getFunctionSymbol(String name) {

        FunctionSymbol cached = functionMap.get(name);
        if(cached != null) {
            return cached;
        }

        if(name.startsWith("$eq_")) {
            Sort sort = new Sort(name.substring(4));
            FunctionSymbol eq = new FunctionSymbol(name, Sort.FORMULA, Arrays.asList(sort, sort));
            functionMap.put(name, eq);
            return eq;
        }

        if(name.matches("\\$len[0-9]+")) {
            String suffix = name.substring(4);
            Sort arraySort = new Sort("array" + suffix);
            FunctionSymbol len = new FunctionSymbol(name, Sort.FORMULA, Arrays.asList(arraySort));
            functionMap.put(name, len);
            return len;
        }

        if(name.matches("[0-9]+")) {
            FunctionSymbol lit = new FunctionSymbol(name, Sort.INT);
            functionMap.put(name, lit);
            return lit;
        }

        throw new RuntimeException();
    }

    @Override
    public SymbolTable addFunctionSymbol(FunctionSymbol symb) {
        return new IncrementalSymbolTable(this, symb);
    }
}
