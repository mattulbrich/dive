package edu.kit.iti.algover.smttrans.data;

import java.util.ArrayList;
import java.util.List;

import edu.kit.iti.algover.term.FunctionSymbol;

import static java.util.Arrays.asList;
//import static edu.kit.iti.algover.smttrans.data.Axiom.*; //TODO later

public enum Operation {

    OR, SETEMPTY, PLUS, MINUS, TIMES, IMP, GT, DIV, LT, EQ, NOT, GE, LE, NEG, ITE, ARR2SELECT, ARRSTORE, ARR2STORE, FIELDSTORE, FIELDSELECT, DECR, SETUNION, SETINTERSECT, SETCARD, SEQCONCAT, ISCREATED, CREATE, ANON, SEQCONS, SEQEMPTY, SEQUPD, SEQGET, SEQLEN, SETIN, SETADD, CONST, ARRLEN, ARR2LEN0, ARR2LEN1, EXISTS, FORALL, LET, ARRSELECT, VAR, HEAP, AND, BV, MOD, AHEAP, EVERYTHING, MULTIUNION, MULTIINTERSECT, MULTIEMPTY, MULTICARD, MULTIADD, MULTIIN, SETMINUS, MULTIMINUS, FUNC;

    private String smt;
    private boolean poly = false;
    private boolean builtin = false;
    private boolean special = false;
    private List<Axiom> instantiations = new ArrayList<>();

    static {

        ARR2LEN0.smt = "arr2len0";
        ARR2LEN0.poly = true;
        ARR2LEN0.instantiations = asList(Axiom.ARR2LEN0, Axiom.ARR2LEN1); // ,Axiom.ARR_2_INST,

        ARR2LEN1.smt = "arr2len1";
        ARR2LEN1.poly = true;
        ARR2LEN1.instantiations = asList(Axiom.HEAP_INST, Axiom.ARR2LEN1, Axiom.ARR2LEN0); // ,Axiom.ARR_2_INST

        ARRLEN.smt = "arrlen";
        ARRLEN.poly = true;
        ARRLEN.instantiations = asList(Axiom.HEAP_INST, Axiom.ARRLEN, Axiom.ARR_2); // ,Axiom.ARR_1_INST

        ARRSELECT.smt = "arrselect";
        ARRSELECT.poly = true;
        ARRSELECT.instantiations = asList(Axiom.HEAP_INST, Axiom.ARR_1, Axiom.ARRSELECT, Axiom.ARRSTORE); // ,Axiom.ARR_1_INST

        ARR2SELECT.smt = "arr2select";
        ARR2SELECT.poly = true;
        ARR2SELECT.instantiations = asList(Axiom.HEAP_INST, Axiom.ARR2_1, Axiom.ARR2STORE, Axiom.ARR2SELECT);

        ARRSTORE.smt = "arrstore";
        ARRSTORE.poly = true;
        ARRSTORE.instantiations = asList(Axiom.HEAP_INST, Axiom.ARR_1, Axiom.ARRSTORE);

        ARR2STORE.smt = "arr2store";
        ARR2STORE.poly = true;
        ARR2STORE.instantiations = asList(Axiom.HEAP_INST, Axiom.ARR2_1, Axiom.ARR2SELECT, Axiom.ARR2STORE);

        SETUNION.smt = "union";
        SETUNION.poly = true;
        SETUNION.instantiations = asList(Axiom.SETEMPTY_INST, Axiom.SET_IN, Axiom.SET_INSERT, Axiom.SET_1, Axiom.SET_2,
                Axiom.SET_UNION, Axiom.SET_2);

        SETADD.smt = "setInsert";
        SETADD.poly = true;
        SETADD.instantiations = asList(Axiom.SETEMPTY_INST, Axiom.SET_IN, Axiom.SET_INSERT, Axiom.SET_1, Axiom.SET_2,
                Axiom.SET_INSERT, Axiom.SET_CARD);
        SETINTERSECT.smt = "intersect";
        SETINTERSECT.poly = true;
        SETINTERSECT.instantiations = asList(Axiom.SETEMPTY_INST, Axiom.SET_IN, Axiom.SET_INSERT, Axiom.SET_1,
                Axiom.SET_2, Axiom.SET_INTERSECT, Axiom.SET_3);

        SETMINUS.smt = "setMinus";
        SETMINUS.poly = true;
        SETCARD.smt = "setcard";
        SETCARD.poly = true;
        SETCARD.instantiations = asList(Axiom.SETEMPTY_INST, Axiom.SET_IN, Axiom.SET_INSERT, Axiom.SET_1, Axiom.SET_2,
                Axiom.SET_CARD, Axiom.SET_CARD, Axiom.SET_CARD_1, Axiom.SET_CARD_2); // ,Axiom.SET_CARD_3,Axiom.SET_CARD_4
        // asList(Axiom.SET_IN,Axiom.SET_1,
        // Axiom.SET_6,Axiom.SET_INSERT,Axiom.SET_CARD,Axiom.SET_CARD_1,Axiom.SET_CARD_2,Axiom.SETEMPTY_INST);
        // //,Axiom.SETEMPTY_INST,Axiom.SET_INST,Axiom.SET_CARD, Axiom.SET_5,
        // Axiom.SETEMPTY_INST, Axiom.SET_CARD_1
        // TODO Axiom.SET_CARD_4 -> timeout
        SETIN.smt = "inSet";
        SETIN.poly = true;
        SETIN.instantiations = asList(Axiom.SETEMPTY_INST, Axiom.SET_IN, Axiom.SET_INSERT, Axiom.SET_1, Axiom.SET_2,
                Axiom.SET_IN);

        
        MULTIUNION.smt = "munion";
        MULTIUNION.poly = true;
        MULTIUNION.instantiations = asList(Axiom.MULTISET_UNION);
        MULTIMINUS.smt = "msetminus";
        MULTIMINUS.poly = true;
        MULTIMINUS.instantiations = asList(Axiom.MULTISET_MINUS);
        MULTIINTERSECT.smt = "mintersect";
        MULTIINTERSECT.poly = true;
        MULTIINTERSECT.instantiations = asList(Axiom.MULTISET_INTERSECT);
        MULTIEMPTY.smt = "msetEmpty";
        MULTIEMPTY.poly = true;
        MULTICARD.smt = "mcard";
        MULTICARD.poly = true;
        
      
        //FUNC.special = false;
        
        
        
        MULTIADD.smt = "msetAdd";
        MULTIADD.poly = true;
        MULTIIN.smt = "inmset";
        MULTIIN.poly = true;
        ISCREATED.smt = "isCreated";
        ISCREATED.poly = true;
        ISCREATED.instantiations = asList();

        CREATE.smt = "create";
        CREATE.poly = true;
        CREATE.instantiations = asList();

        ANON.smt = "anon";
        ANON.instantiations = asList(Axiom.ANON); // Axiom.HEAP_4
        // ANON.special = true;

        MOD.smt = "mod";
        // MOD.instantiations = asList(Axiom.MODH); // Axiom.MODH
        MOD.special = true;

        AHEAP.smt = "aheap";
        AHEAP.instantiations = asList();
        // AHEAP.special = true;

        HEAP.smt = "heap";
        // HEAP.instantiations = asList(Axiom.HEAP_INST); // Axiom.HEAP_INST
        HEAP.special = true;

        DECR.smt = "decr";

        SEQEMPTY.smt = "seqEmpty";
        SEQEMPTY.poly = true;
        SEQEMPTY.instantiations = asList(Axiom.SEQ_LEN); //Axiom.SEQ_LEN_5

        SETEMPTY.smt = "setEmpty";
        SETEMPTY.poly = true;
        SETEMPTY.instantiations = asList(Axiom.SET_0,Axiom.SET_CARD, Axiom.SET_CARD_1);

        EVERYTHING.smt = "everything";
        EVERYTHING.instantiations = asList(Axiom.SET_IN, Axiom.SET_INSERT, Axiom.SET_1, Axiom.EVERYTHING); //
        EVERYTHING.special = true;

        SEQCONS.smt = "seqcons";
        SEQCONS.poly = true;
        SEQCONS.instantiations = asList(Axiom.SEQ_CONS, Axiom.SEQ_6, Axiom.SEQ_7);

        SEQUPD.smt = "seqstore";
        SEQUPD.poly = true;
        SEQUPD.instantiations = asList(Axiom.SEQEMTY_INST, Axiom.SEQ_STORE, Axiom.SEQ_0);

        SEQGET.smt = "seqget";
        SEQGET.poly = true;
        SEQGET.instantiations = asList(Axiom.SEQEMTY_INST, Axiom.SEQ_GET, Axiom.SEQ_4);

        SEQLEN.smt = "seqlen";
        SEQLEN.poly = true;
        SEQLEN.instantiations = asList(Axiom.SEQEMTY_INST, Axiom.SEQ_LEN, Axiom.SEQ_LEN_1);

        SEQCONCAT.smt = "seqconcat";
        SEQCONCAT.poly = true;
        SEQCONCAT.instantiations = asList(Axiom.SEQEMTY_INST, Axiom.SEQ_CONCAT, Axiom.SEQ_LEN, Axiom.SEQ_LEN_5);

        FIELDSTORE.smt = "fieldstore";
        FIELDSTORE.poly = true;
        FIELDSTORE.instantiations = asList(Axiom.HEAP_1, Axiom.HEAP_INST, Axiom.FIELDSTORE, Axiom.FIELDSELECT);

        FIELDSELECT.smt = "fieldselect";
        FIELDSELECT.poly = true;
        FIELDSELECT.instantiations = asList(Axiom.HEAP_1, Axiom.HEAP_INST, Axiom.FIELDSELECT, Axiom.FIELDSTORE);

        /**
         * 
         */

        FORALL.smt = "forall";
        FORALL.builtin = true;

        EXISTS.smt = "exists";
        EXISTS.builtin = true;

        AND.smt = "and";
        AND.builtin = true;

        OR.smt = "or";
        OR.builtin = true;

        IMP.smt = "=>";
        IMP.builtin = true;
        PLUS.smt = "+";
        PLUS.builtin = true;
        MINUS.smt = "-";
        MINUS.builtin = true;

        TIMES.smt = "*";
        TIMES.builtin = true;
        GT.smt = ">";
        GT.builtin = true;
        LT.smt = "<";
        LT.builtin = true;
        EQ.smt = "=";
        EQ.builtin = true;
        NOT.smt = "not";
        NOT.builtin = true;
        DIV.smt = "/";
        DIV.builtin = true;
        GE.smt = ">=";
        GE.builtin = true;
        LE.smt = "<=";
        LE.builtin = true;
        NEG.smt = "-";
        NEG.builtin = true;
        ITE.smt = "ite";
        ITE.builtin = true;

    }

    
    public void setSMT(String s) {
        this.smt = s;
    }
    public String toSMT() {
        return smt;
    }

    public boolean isPoly() {
        return poly;
    }

    public boolean isSpecial() {
        return special;
    }

    public boolean isBuiltIn() {
        return builtin;
    }

    public List<Axiom> getInstantiations() {
        return instantiations;
    }

}
