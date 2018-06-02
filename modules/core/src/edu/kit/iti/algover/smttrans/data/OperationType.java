package edu.kit.iti.algover.smttrans.data;

public enum OperationType {

    ARR, ARR2, SET, MULTISET, INT, BOOL, SORT, ANY, NONE, SEQ;

    private String smt;

    static {
        ARR.smt = "Arr";
        ARR2.smt = "Arr2";
        SET.smt = "Set";
        MULTISET.smt = "mSet";
        INT.smt = "Int";
        BOOL.smt = "Bool";
        SEQ.smt = "Seqq";
    }



    public String getSMT() {
        return smt;
    }
}
