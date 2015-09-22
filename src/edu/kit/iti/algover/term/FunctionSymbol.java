package edu.kit.iti.algover.term;

import java.util.List;

import edu.kit.iti.algover.util.Util;

public class FunctionSymbol {

    private final Sort resultSort;
    private final Sort[] argumentSorts;

    public FunctionSymbol(String name, Sort resultSort, Sort... argumentSorts) {
        this.name = name;
        this.resultSort = resultSort;
        this.argumentSorts = argumentSorts;
    }

    public FunctionSymbol(String name, Sort resultSort, List<Sort> argumentSorts) {
        this(name, resultSort, argumentSorts.toArray(new Sort[argumentSorts.size()]));
    }

    public List<Sort> getArgumentSorts() {
        return Util.readOnlyArrayList(argumentSorts);
    }

    private String name;

    public Sort getResultSort() {
        return resultSort;
    }

    public int getArity() {
        return argumentSorts.length;
    }

    public String getName() {
        return name;
    }

}
