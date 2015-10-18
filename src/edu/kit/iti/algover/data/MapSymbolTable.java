package edu.kit.iti.algover.data;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
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
            FunctionSymbol len = new FunctionSymbol(name, Sort.INT, Arrays.asList(arraySort));
            functionMap.put(name, len);
            return len;
        }

        if(name.matches("[0-9]+")) {
            FunctionSymbol lit = new FunctionSymbol(name, Sort.INT);
            functionMap.put(name, lit);
            return lit;
        }

        if(name.matches("\\$select[0-9]+")) {
            String suffix = name.substring(7);
            int dim = Integer.parseInt(suffix);
            Sort arraySort = new Sort("array" + suffix);
            List<Sort> args = new ArrayList<>();
            args.add(arraySort);
            args.addAll(Collections.nCopies(dim, Sort.INT));
            FunctionSymbol len = new FunctionSymbol(name, Sort.INT, args);
            functionMap.put(name, len);
            return len;
        }

        throw new RuntimeException("The function symbol " + name + " cannot be found");
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
