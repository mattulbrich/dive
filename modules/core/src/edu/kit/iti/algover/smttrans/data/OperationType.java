package edu.kit.iti.algover.smttrans.data;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public enum OperationType {

    ARR, ARR2, SET, MULTISET, INT, BOOL, SORT, ANY, NONE, SEQ;

    private String smt;
    private List<String> dependencies = new ArrayList<>();

    static {
        ARR.smt = "Arr";
        ARR.dependencies = Arrays.asList("(declare-sort Heap)","(declare-const heap Heap)");
        ARR2.smt = "Arr2";
        SET.smt = "Set";
        MULTISET.smt = "mSet";
        INT.smt = "Int";
        BOOL.smt = "Bool";
        SEQ.smt = "Seqq";
        SORT.smt = "SORT";
        ANY.smt = "ANY";
        NONE.smt = "NONE";
    }

    public String getSMT() {
        return smt;
    }
    
    public List<String> getDependencies() {
        return dependencies;
    }
}
