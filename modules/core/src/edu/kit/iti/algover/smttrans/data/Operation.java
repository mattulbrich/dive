package edu.kit.iti.algover.smttrans.data;

import java.util.ArrayList;
import java.util.List;

import edu.kit.iti.algover.term.FunctionSymbol;

import static java.util.Arrays.asList;
//import static edu.kit.iti.algover.smttrans.data.Axiom.*; //TODO later

public enum Operation {

  OR, SETEMPTY, PLUS, MINUS, TIMES, IMP, GT, LT, EQ, NOT, GE, LE, NEG, ITE, ARR2SELECT, ARRSTORE, ARR2STORE, FIELDSTORE, FIELDSELECT, DECR, SETUNION, SETINTERSECT, SETCARD, SEQCONCAT, ISCREATED, CREATE, ANON, SEQCONS, SEQEMPTY, SEQUPD, SEQGET, SEQLEN, SETIN, SETADD, CONST, ARRLEN, ARR2LEN0, ARR2LEN1, EXISTS, FORALL, LET, ARRSELECT, VAR, HEAP, AND, BV, MOD, AHEAP, EVERYTHING;

    private String smt;
    private Boolean poly;
   
    private List<Axiom> instantiations = new ArrayList<>();

    static {

        
        EVERYTHING.smt = "everything";
        EVERYTHING.poly = false;
        EVERYTHING.instantiations = asList(); //Axiom.EVERYTHING

        ARR2LEN0.smt = "arr2len0";
        ARR2LEN0.poly = true;
        ARR2LEN0.instantiations = asList(Axiom.ARR2LEN0, Axiom.ARR2LEN1); //,Axiom.ARR_2_INST,

        ARR2LEN1.smt = "arr2len1";
        ARR2LEN1.poly = true;
        ARR2LEN1.instantiations = asList(Axiom.HEAP_INST, Axiom.HEAP_INST_2,Axiom.ARR2LEN1,Axiom.ARR2LEN0); //,Axiom.ARR_2_INST

       
        ARRLEN.smt = "arrlen";
        ARRLEN.poly = true;
        ARRLEN.instantiations = asList(Axiom.HEAP_INST, Axiom.HEAP_INST_2, Axiom.ARRLEN, Axiom.ARR_2); //,Axiom.ARR_1_INST

        ARRSELECT.smt = "arrselect";
        ARRSELECT.poly = true;
        ARRSELECT.instantiations = asList(Axiom.HEAP_INST, Axiom.HEAP_INST_2 ,Axiom.ARR_1, Axiom.ARRSELECT, Axiom.ARRSTORE); //,Axiom.ARR_1_INST

        ARR2SELECT.smt = "arr2select";
        ARR2SELECT.poly = true;
        ARR2SELECT.instantiations = asList(Axiom.HEAP_INST, Axiom.HEAP_INST_2,Axiom.ARR2_1,Axiom.ARR2STORE, Axiom.ARR2SELECT);

        ARRSTORE.smt = "arrstore";
        ARRSTORE.poly = true;
        ARRSTORE.instantiations = asList(Axiom.HEAP_INST, Axiom.HEAP_INST_2,Axiom.ARR_1, Axiom.ARRSTORE);

        ARR2STORE.smt = "arr2store";
        ARR2STORE.poly = true;
        ARR2STORE.instantiations = asList(Axiom.HEAP_INST, Axiom.HEAP_INST_2,Axiom.ARR2_1, Axiom.ARR2SELECT,Axiom.ARR2STORE);
        
        SETUNION.smt = "union";
        SETUNION.poly = true;
        SETUNION.instantiations = asList(Axiom.SETEMPTY_INST,Axiom.SET_IN,Axiom.SET_INSERT,Axiom.SET_1,Axiom.SET_2,Axiom.SET_8,Axiom.SET_UNION,Axiom.SET_2);

        SETADD.smt = "setInsert";
        SETADD.poly = true;
        SETADD.instantiations = asList(Axiom.SETEMPTY_INST,Axiom.SET_IN,Axiom.SET_INSERT,Axiom.SET_1,Axiom.SET_2,Axiom.SET_8,Axiom.SET_INSERT,Axiom.SET_CARD);
        SETINTERSECT.smt = "intersect";
        SETINTERSECT.poly = true;
        SETINTERSECT.instantiations = asList(Axiom.SETEMPTY_INST,Axiom.SET_IN,Axiom.SET_INSERT,Axiom.SET_1,Axiom.SET_2,Axiom.SET_8,Axiom.SET_INTERSECT,Axiom.SET_3);

        SETCARD.smt = "setcard";
        SETCARD.poly = true;
        SETCARD.instantiations = asList(Axiom.SETEMPTY_INST,Axiom.SET_IN,Axiom.SET_INSERT,Axiom.SET_1,Axiom.SET_2,Axiom.SET_8,Axiom.SET_CARD,Axiom.SET_CARD,Axiom.SET_CARD_1,Axiom.SET_CARD_2); //,Axiom.SET_CARD_3,Axiom.SET_CARD_4
        //asList(Axiom.SET_IN,Axiom.SET_1, Axiom.SET_6,Axiom.SET_INSERT,Axiom.SET_CARD,Axiom.SET_CARD_1,Axiom.SET_CARD_2,Axiom.SETEMPTY_INST); //,Axiom.SETEMPTY_INST,Axiom.SET_INST,Axiom.SET_CARD, Axiom.SET_5, Axiom.SETEMPTY_INST, Axiom.SET_CARD_1
        // TODO Axiom.SET_CARD_4 -> timeout
        SETIN.smt = "inSet";
        SETIN.poly = true;
        SETIN.instantiations = asList(Axiom.SETEMPTY_INST,Axiom.SET_IN,Axiom.SET_INSERT,Axiom.SET_1,Axiom.SET_2,Axiom.SET_8,Axiom.SET_IN);

        ISCREATED.smt = "isCreated";
        ISCREATED.poly = true;
        ISCREATED.instantiations = asList();

        CREATE.smt = "create";
        CREATE.poly = true;
        CREATE.instantiations = asList();

        ANON.smt = "anon";
        ANON.poly = false;
        ANON.instantiations = asList(Axiom.ANON); //Axiom.HEAP_4

        MOD.smt = "modh";
        MOD.poly = false;
        MOD.instantiations=asList(Axiom.MODH); //Axiom.MODH
        
        AHEAP.smt = "aheap";
        AHEAP.poly = false;
        AHEAP.instantiations=asList();
        
        SEQCONS.smt = "SEQCONS";
        SEQCONS.poly = true;
        SEQCONS.instantiations = asList(Axiom.SEQEMTY_INST); //TODO

        SEQEMPTY.smt = "seqEmpty";
        SEQEMPTY.poly = true;
        SEQEMPTY.instantiations = asList(Axiom.SEQEMTY_INST,Axiom.SEQ_LEN,Axiom.SEQ_LEN_5);
        
        SETEMPTY.smt = "setEmpty";
        SETEMPTY.poly = true;
        SETEMPTY.instantiations = asList(Axiom.SETEMPTY_INST,Axiom.SET_CARD,Axiom.SET_8,Axiom.SET_CARD_1);
        

        SEQUPD.smt = "seqstore";
        SEQUPD.poly = true;
        SEQUPD.instantiations = asList(Axiom.SEQEMTY_INST, Axiom.SEQ_STORE,Axiom.SEQ_0);

        SEQGET.smt = "seqget";
        SEQGET.poly = true;
        SEQGET.instantiations = asList(Axiom.SEQEMTY_INST,Axiom.SEQ_GET,Axiom.SEQ_4);

        SEQLEN.smt = "seqlen";
        SEQLEN.poly = true;
        SEQLEN.instantiations = asList(Axiom.SEQEMTY_INST,Axiom.SEQ_LEN, Axiom.SEQ_LEN_1);

        SEQCONCAT.smt = "seqconcat";
        SEQCONCAT.poly = true;
        SEQCONCAT.instantiations = asList(Axiom.SEQEMTY_INST,Axiom.SEQ_CONCAT,Axiom.SEQ_LEN,Axiom.SEQ_LEN_5);

        HEAP.smt = "heap";
        HEAP.poly = false;
        HEAP.instantiations = asList(Axiom.HEAP_INST, Axiom.HEAP_INST_2); //Axiom.HEAP_INST

        FIELDSTORE.smt = "fieldstore";
        FIELDSTORE.poly = true;
        FIELDSTORE.instantiations = asList(Axiom.HEAP_1,Axiom.HEAP_INST,Axiom.HEAP_INST_2,Axiom.FIELDSTORE,Axiom.FIELDSELECT);

        FIELDSELECT.smt = "fieldselect";
        FIELDSELECT.poly = true;
        FIELDSELECT.instantiations = asList(Axiom.HEAP_1,Axiom.HEAP_INST,Axiom.HEAP_INST_2,Axiom.FIELDSELECT,Axiom.FIELDSTORE);

        /**
         * 
         */

        FORALL.smt = "forall";
        FORALL.poly = false;

        EXISTS.smt = "exists";
        EXISTS.poly = false;

        AND.smt = "and";
        AND.poly = false;
        
        OR.smt = "or";
        OR.poly = false;

        IMP.smt = "=>";
        IMP.poly = false;

        PLUS.smt = "+";
        PLUS.poly = false;

        MINUS.smt = "-";
        MINUS.poly = false;

        TIMES.smt = "*";
        TIMES.poly = false;

        GT.smt = ">";
        GT.poly = false;

        LT.smt = "<";
        LT.poly = false;

        EQ.smt = "=";
        EQ.poly = false;

        NOT.smt = "not";
        NOT.poly = false;

        GE.smt = ">=";
        GE.poly = false;


        LE.smt = "<=";
        LE.poly = false;


        NEG.smt = "-";
        NEG.poly = false;


        ITE.smt = "ITE";
        ITE.poly = false;

        DECR.smt = "DECR";
        DECR.poly = false;

    }

    public String toSMT() {
        return smt;
    }

    public Boolean isPoly() {
        return poly;
    }



    public List<Axiom> getInstantiations() {
        return instantiations;
    }

}
