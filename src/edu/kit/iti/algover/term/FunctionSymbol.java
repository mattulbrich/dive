package edu.kit.iti.algover.term;

import java.util.List;

import edu.kit.iti.algover.util.Util;

public class FunctionSymbol {

    private Sort resultSort;
    private Sort[] argumentSorts;

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
