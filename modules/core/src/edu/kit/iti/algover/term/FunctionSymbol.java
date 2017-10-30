/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term;

import java.util.Arrays;
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

    @Override
    public int hashCode() {
        int result = resultSort.hashCode();
        result = 31 * result + Arrays.hashCode(argumentSorts);
        result = 31 * result + name.hashCode();
        return result;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        FunctionSymbol that = (FunctionSymbol) o;

        if (!resultSort.equals(that.resultSort)) return false;
        if (!Arrays.equals(argumentSorts, that.argumentSorts)) return false;
        return name.equals(that.name);
    }

    public String getName() {
        return name;
    }

    @Override
    public String toString() {
        return name + "(" + Util.join(argumentSorts, ", ") + ") : " + resultSort;
     }

}
