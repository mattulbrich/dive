package edu.kit.iti.algover.smttrans.data;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import edu.kit.iti.algover.term.FunctionSymbol;

import static java.util.Arrays.asList;
//import static edu.kit.iti.algover.smttrans.data.Axiom.*; //TODO later

public enum Operation {

    OR, SETEMPTY, PLUS, MINUS, TIMES, IMP, GT, DIV, LT, EQ, NOT, GE, LE, NEG, ITE, ARR2SELECT, ARRSTORE, ARR2STORE, FIELDSTORE, FIELDSELECT, DECR, SETUNION, SETINTERSECT, SETCARD, SEQCONCAT, ISCREATED, CREATE, ANON, SEQCONS, SEQEMPTY, SEQUPD, SEQGET, SEQLEN, SETIN, SETADD, CONST, ARRLEN, ARR2LEN0, ARR2LEN1, EXISTS, FORALL, LET, ARRSELECT, VAR, HEAP, AND, BV, MOD, AHEAP, EVERYTHING, MULTIUNION, MULTIINTERSECT, MULTIEMPTY, MULTICARD, MULTIADD, MULTIIN, SETMINUS, MULTIMINUS, FUNC, SEQSUBSELECT, SETSUBSET;

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

        SETUNION.smt = "setunion";
        SETUNION.poly = true;
        SETUNION.instantiations = asList(Axiom.S2, Axiom.S3, Axiom.S4);

        SETADD.smt = "setadd";
        SETADD.poly = true;
        SETADD.instantiations = asList(Axiom.S2, Axiom.S3); // Axiom.SETCARD
        SETINTERSECT.smt = "setintersect";
        SETINTERSECT.poly = true;
        SETINTERSECT.instantiations = asList(Axiom.S2, Axiom.S3, Axiom.S5);
        
        SETSUBSET.smt = "setsubset";
        SETSUBSET.poly = true;
        SETSUBSET.instantiations = asList(Axiom.S7);
        
        SETMINUS.smt = "setminus";
        SETMINUS.poly = true;
        SETMINUS.instantiations = asList(Axiom.S6);
        SETCARD.smt = "setcard";
        SETCARD.poly = true;
        SETCARD.instantiations = asList(Axiom.SC1, Axiom.SC3);
        SETIN.smt = "setin";
        SETIN.poly = true;
        SETIN.instantiations = asList(Axiom.S2); // ,Axiom.S3
        SETEMPTY.smt = "setempty";
        SETEMPTY.poly = true;
        SETEMPTY.instantiations = asList(Axiom.S1, Axiom.S2, Axiom.S3,Axiom.SC2);

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

        // FUNC.special = false;

        MULTIADD.smt = "msetAdd";
        MULTIADD.poly = true;
        MULTIIN.smt = "inmset";
        MULTIIN.poly = true;
        ISCREATED.smt = "isCreated";
        ISCREATED.poly = false;
        ISCREATED.instantiations = asList(Axiom.CREATED, Axiom.CREATE, Axiom.HEAP_3);

        CREATE.smt = "create";
        CREATE.poly = false;
        CREATE.instantiations = asList(Axiom.CREATED, Axiom.CREATE, Axiom.HEAP_3);

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

        SEQEMPTY.smt = "seqempty";
        SEQEMPTY.poly = true;
        SEQEMPTY.instantiations = asList(Axiom.SQL1, Axiom.SQL2);

        EVERYTHING.smt = "everything";
        EVERYTHING.instantiations = asList(Axiom.EVERYTHING); //
        EVERYTHING.special = true;

        SEQCONS.smt = "seqcons";
        SEQCONS.poly = true;
        SEQCONS.instantiations = asList(Axiom.SQ2, Axiom.SQL5);

        SEQUPD.smt = "sequpd";
        SEQUPD.poly = true;
        SEQUPD.instantiations = asList(Axiom.SQ1);

        SEQGET.smt = "seqget";
        SEQGET.poly = true;
        SEQGET.instantiations = asList(Axiom.SQ1);

        SEQSUBSELECT.smt = "seqsubselect";
        SEQSUBSELECT.poly = true;
        SEQSUBSELECT.instantiations = asList(Axiom.SQ4, Axiom.SQL3);

        SEQLEN.smt = "seqlen";
        SEQLEN.poly = true;
        SEQLEN.instantiations = asList(Axiom.SQL2);

        SEQCONCAT.smt = "seqconcat";
        SEQCONCAT.poly = true;
        SEQCONCAT.instantiations = asList(Axiom.SQ3, Axiom.SQL4);

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
        Set<Axiom> r = new LinkedHashSet<>();
        Set<Axiom> d = new LinkedHashSet<>();
        r.addAll(instantiations);
        while (true) {
            for (Axiom a : r) {
                d.addAll(a.getDependencies());
            }
            if (r.containsAll(d)) {
                return new ArrayList<>(r);
            } else {
                r.addAll(d);
                
            }

        }

    }

}
