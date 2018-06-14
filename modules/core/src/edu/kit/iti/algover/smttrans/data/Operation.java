package edu.kit.iti.algover.smttrans.data;

import java.util.ArrayList;
import java.util.List;

import edu.kit.iti.algover.term.FunctionSymbol;

import static java.util.Arrays.asList;
//import static edu.kit.iti.algover.smttrans.data.Axiom.*; //TODO later

public enum Operation {

    PLUS, MINUS, TIMES, IMP, GT, LT, EQ, NOT, GE, LE, NEG, ITE, ARR2SELECT, ARRSTORE, ARR2STORE, FIELDSTORE, FIELDSELECT, DECR, SETUNION, SETINTERSECT, SETCARD, SEQCONCAT, ISCREATED, CREATE, ANON, SEQCONS, SEQEMPTY, SEQUPD, SEQGET, SEQLEN, SETIN, SETADD, CONST, ARRLEN, ARR2LEN0, ARR2LEN1, EXISTS, FORALL, LET, ARRSELECT, VAR, HEAP, AND, BV, MOD, AHEAP;

    private String smt;
    private Boolean poly;
    private OperationType type;
    private List<Axiom> instantiations = new ArrayList<>();

    static {

        ARR2LEN0.smt = "arr2len0";
        ARR2LEN0.poly = true;
        ARR2LEN0.type = OperationType.ARR2;
        ARR2LEN0.instantiations = asList(Axiom.ARR2LEN0);

        ARR2LEN1.smt = "arr2len1";
        ARR2LEN1.poly = true;
        ARR2LEN1.type = OperationType.ARR2;
        ARR2LEN1.instantiations = asList(Axiom.ARR2LEN1);

        ARRLEN.smt = "arrlen";
        ARRLEN.poly = true;
        ARRLEN.type = OperationType.ARR;
        ARRLEN.instantiations = asList(Axiom.ARR_1, Axiom.ARRLEN, Axiom.ARR_2, Axiom.ARRSTORE, Axiom.ARRSELECT);

        ARRSELECT.smt = "arrselect";
        ARRSELECT.poly = true;
        ARRSELECT.type = OperationType.ARR;
        ARRSELECT.instantiations = asList(Axiom.ARR_1, Axiom.ARRSELECT, Axiom.ARRSTORE);

        ARR2SELECT.smt = "arr2select";
        ARR2SELECT.poly = true;
        ARR2SELECT.type = OperationType.ARR2;
        ARR2SELECT.instantiations = asList(Axiom.ARR2_1, Axiom.ARR2SELECT);

        ARRSTORE.smt = "arrstore";
        ARRSTORE.poly = true;
        ARRSTORE.type = OperationType.ARR;
        ARRSTORE.instantiations = asList(Axiom.ARR_1, Axiom.ARRSTORE);

        ARR2STORE.smt = "arr2store";
        ARR2STORE.poly = true;
        ARR2STORE.type = OperationType.ARR2;
        ARR2STORE.instantiations = asList(Axiom.ARR2_1, Axiom.ARR2STORE);

        SETUNION.smt = "union";
        SETUNION.poly = true;
        SETUNION.type = OperationType.SET;
        SETUNION.instantiations = asList(Axiom.SET_UNION,Axiom.SET_2);

        SETINTERSECT.smt = "intersect";
        SETINTERSECT.poly = true;
        SETINTERSECT.type = OperationType.SET;
        SETINTERSECT.instantiations = asList(Axiom.SET_INTERSECT);

        SETCARD.smt = "setcard";
        SETCARD.poly = true;
        SETCARD.type = OperationType.SET;
        SETCARD.instantiations = asList(Axiom.SET_IN,Axiom.SET_1, Axiom.SET_6,Axiom.SET_INSERT,Axiom.SET_CARD,Axiom.SET_CARD_1,Axiom.SET_CARD_2,Axiom.SETEMPTY_INST); //,Axiom.SETEMPTY_INST,Axiom.SET_INST,Axiom.SET_CARD, Axiom.SET_5, Axiom.SETEMPTY_INST, Axiom.SET_CARD_1
        // TODO Axiom.SET_CARD_4 -> timeout
        SETIN.smt = "select";
        SETIN.poly = true;
        SETIN.type = OperationType.SET;
        SETIN.instantiations = asList();

        ISCREATED.smt = "isCreated";
        ISCREATED.poly = true;
        ISCREATED.type = OperationType.SORT;
        ISCREATED.instantiations = asList();

        CREATE.smt = "create";
        CREATE.poly = true;
        CREATE.type = OperationType.SORT;
        CREATE.instantiations = asList();

        ANON.smt = "";
        ANON.poly = false;
        ANON.type = OperationType.SORT;
        ANON.instantiations = asList();

        MOD.smt = "";
        MOD.poly = false;
        MOD.type = OperationType.SET;
        MOD.instantiations=asList();
        
        AHEAP.smt = "aheap";
        AHEAP.poly = false;
        AHEAP.type = OperationType.SORT;
        AHEAP.instantiations=asList();
        
        SEQCONS.smt = "";
        SEQCONS.poly = true;
        SEQCONS.type = OperationType.SEQ;
        SEQCONS.instantiations = asList();

        SEQEMPTY.smt = "emptyseq";
        SEQEMPTY.poly = true;
        SEQEMPTY.type = OperationType.SEQ;
        SEQEMPTY.instantiations = asList();

        SEQUPD.smt = "seqstore";
        SEQUPD.poly = true;
        SEQUPD.type = OperationType.SEQ;
        SEQUPD.instantiations = asList();

        SEQGET.smt = "seqget";
        SEQGET.poly = true;
        SEQGET.type = OperationType.SEQ;
        SEQGET.instantiations = asList();

        SEQLEN.smt = "seqlen";
        SEQLEN.poly = true;
        SEQLEN.type = OperationType.SEQ;
        SEQLEN.instantiations = asList(Axiom.SEQ_LEN);

        SEQCONCAT.smt = "seqconcat";
        SEQCONCAT.poly = true;
        SEQCONCAT.type = OperationType.SEQ;
        SEQCONCAT.instantiations = asList(Axiom.SEQ_CONCAT);

        HEAP.smt = "heap"; // TODO
        HEAP.poly = false;
        HEAP.type = OperationType.SORT;
        HEAP.instantiations = asList();

        FIELDSTORE.smt = "fieldstore";
        FIELDSTORE.poly = true;
        FIELDSTORE.type = OperationType.SORT;
        FIELDSTORE.instantiations = asList(Axiom.HEAP_1,Axiom.FIELDSTORE,Axiom.FIELDSELECT);

        FIELDSELECT.smt = "fieldselect";
        FIELDSELECT.poly = true;
        FIELDSELECT.type = OperationType.SORT;
        FIELDSELECT.instantiations = asList(Axiom.HEAP_1,Axiom.FIELDSELECT,Axiom.FIELDSTORE);

        /**
         * 
         */

        FORALL.smt = "forall";
        FORALL.poly = false;
        FORALL.type = OperationType.NONE;

        EXISTS.smt = "exists";
        EXISTS.poly = false;
        EXISTS.type = OperationType.NONE;

        AND.smt = "and";
        AND.poly = false;
        AND.type = OperationType.NONE;

        IMP.smt = "=>";
        IMP.poly = false;
        IMP.type = OperationType.NONE;

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

        DECR.smt = "";
        DECR.poly = false;

    }

    public String toSMT() {
        return smt;
    }

    public Boolean isPoly() {
        return poly;
    }

    public OperationType getType() {
        return type;
    }

    public List<Axiom> getInstantiations() {
        return instantiations;
    }

}
