package edu.kit.iti.algover.smttrans.data;

import java.util.ArrayList;

import java.util.List;

import edu.kit.iti.algover.smttrans.translate.Type;

public enum Operation {

    PLUS, MINUS, TIMES, GT, LT, EQ, NOT, GE, LE, NEG, ITE, ARR2SELECT, ARRSTORE, ARR2STORE, FIELDSTORE, FIELDSELECT, DECR, SETUNION, SETINTERSECT, SETCARD, SEQCONCAT, ISCREATED, CREATE, ANON, SEQCONS, SEQEMPTY, SEQUPD, SEQGET, SEQLEN, SETIN, SETADD, CONST, ARRLEN, ARR2LEN0, ARR2LEN1, EXISTS, FORALL, LET, ARRSELECT, VAR;

    private String smt;
    private Boolean poly;
    private OperationType type;
    private List<Axiom> instantiations = new ArrayList<>();

    static {

        ARRSELECT.smt = "arrselect";
        ARRSELECT.poly = true;
        ARR2SELECT.type = OperationType.ARR;
        ARR2LEN0.smt = "arr2len0";
        ARR2LEN0.poly = true;
        ARR2LEN0.type = OperationType.ARR2;

        ARR2LEN1.smt = "arr2len1";
        ARR2LEN1.poly = true;
        ARR2LEN1.type = OperationType.ARR2;

        ARRLEN.smt = "arrlen";
        ARRLEN.poly = true;
        ARRLEN.type = OperationType.ARR;

        PLUS.smt = "+";
        PLUS.poly = false;
        PLUS.type = OperationType.INT;

        MINUS.smt = "-";
        MINUS.poly = false;
        MINUS.type = OperationType.INT;

        TIMES.smt = "*";
        TIMES.poly = false;
        TIMES.type = OperationType.INT;

        GT.smt = ">";
        GT.poly = false;
        GT.type = OperationType.INT;

        LT.smt = "<";
        LT.poly = false;
        LT.type = OperationType.INT;

        EQ.smt = "=";
        EQ.poly = false;
        EQ.type = OperationType.ANY;

        NOT.smt = "not";
        NOT.poly = false;
        NOT.type = OperationType.BOOL;

        GE.smt = ">=";
        GE.poly = false;
        GE.type = OperationType.INT;

        LE.smt = "<=";
        LE.poly = false;
        LE.type = OperationType.INT;

        NEG.smt = "";
        NEG.poly = false;
        NEG.type = OperationType.INT;

        ITE.smt = "";
        ITE.poly = false;

        ARR2SELECT.smt = "";
        ARR2SELECT.poly = true;
        ARR2SELECT.type = OperationType.ARR2;

        ARRSTORE.smt = "";
        ARRSTORE.poly = true;
        ARRSTORE.type = OperationType.ARR;

        ARR2STORE.smt = "";
        ARR2STORE.poly = true;
        ARR2STORE.type = OperationType.ARR2;

        FIELDSTORE.smt = "";
        FIELDSTORE.poly = true;
        FIELDSTORE.type = OperationType.SORT;

        FIELDSELECT.smt = "";
        FIELDSELECT.poly = true;
        FIELDSELECT.type = OperationType.SORT;

        DECR.smt = "";
        DECR.poly = false;

        SETUNION.smt = "";
        SETUNION.poly = true;
        SETUNION.type = OperationType.SET;

        SETINTERSECT.smt = "";
        SETINTERSECT.poly = true;
        SETINTERSECT.type = OperationType.SET;

        SETCARD.smt = "";
        SETCARD.poly = true;
        SETCARD.type = OperationType.SET;

        SEQCONCAT.smt = "";
        SEQCONCAT.poly = true;
        SEQCONCAT.type = OperationType.SEQ;

        ISCREATED.smt = "";
        ISCREATED.poly = true;
        ISCREATED.type = OperationType.SORT;

        CREATE.smt = "";
        CREATE.poly = true;
        CREATE.type = OperationType.SORT;

        ANON.smt = "";
        ANON.poly = false;
        ANON.type = OperationType.SORT;

        SEQCONS.smt = "";
        SEQCONS.poly = true;
        SEQCONS.type = OperationType.SEQ;

        SEQEMPTY.smt = "";
        SEQEMPTY.poly = true;
        SEQEMPTY.type = OperationType.SEQ;

        SEQUPD.smt = "";
        SEQUPD.poly = true;
        SEQUPD.type = OperationType.SEQ;

        SEQGET.smt = "";
        SEQGET.poly = true;
        SEQGET.type = OperationType.SEQ;

        SEQLEN.smt = "";
        SEQLEN.poly = true;
        SEQLEN.type = OperationType.SEQ;

        SETIN.smt = "";
        SETIN.poly = true;
        SETIN.type = OperationType.SET;

        SETADD.smt = "";
        SETADD.poly = true;
        SETADD.type = OperationType.SET;
    }

    public String toSMTLib(Type type) {
        // special cases here ...

        if (poly) {
            return smt + type.toString();
        }
        return smt;
    }

    public Boolean isPoly() {
        return poly;
    }
    
    public OperationType getType() {
        return type;
    }

}
