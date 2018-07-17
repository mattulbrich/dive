package edu.kit.iti.algover.smttrans.data;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import edu.kit.iti.algover.smttrans.translate.Names;

public enum Axiom {

    /**
     * Sorts
     */

    // sets
    // SET_INST,
    // SETEMPTY_INST,

    // multisets
    MULTISET_INST, MULTISETEMTPY_INST,

    // sequences

    // Heap/Arrays
    FIELD_INST, HEAP_INST, TYPE_INST, OBJECT_INST, // ARR_1_INST, //ARR_2_INST
    TYPE_CONST, EVERYTHING,

    /**
     * Functions
     */

    // sets
    SETIN, SETADD, SETCARD, SETMINUS, SETUNION, SETINTERSECT, SETSUBSET,

    // multisets
    MULTISET_UNION, MULTISET_INTERSECT, MULTISET_MINUS, MULTISET_CARD, MULTISET_SUBSET, MULTISET_INSERT, MULTISET_SELECT, MULTISET_IN, MULTISET_SINGLE, MULTISET_MAX, MULTISET_MIN,

    // sequences
    SEQLEN, SEQGET, SEQUPD, SEQCONS, SEQSUBSELECT, SEQCONCAT,
    // Heap/Arrays
    O2C, C2O, FIELDSTORE, FIELDSELECT, ANON, CREATE, CREATED, MODH, ARRSELECT, ARR2SELECT, ARR2STORE, ARR2LEN0, ARR2LEN1, ARRLEN, ARRSTORE, TYPEOF,

    /**
     * Axioms
     */

    // sets
    S1, S2, S3, S4, S5, S6, S7, SC1, SC2, SC3,

    // multisets
    MULTISET_1, MULTISET_2, MULTISET_3, MULTISET_4, MULTISET_5, MULTISET_6, MULTISET_7, MULTISET_8, MULTISET_CARD_1, MULTISET_CARD_2, MULTISET_CARD_3, MULTISET_CARD_4,

    // sequences

    SQ1, SQ2, SQ3, SQ4, SQ5, SQ6, SQL1, SQL2, SQL3, SQL4, SQL5,

    // Heap/Arrays
    ARR_1, ARR_2, ARR2_1, HEAP_1, HEAP_2, HEAP_3, HEAP_4, HEAP_5, HEAP_6;

    static {

        /**
         * Sorts
         */

        // sets
        // SET_INST.smt = "(define-sort Set (T) (Array T Bool))"; //TODO
        // SETEMPTY_INST.smt = "(declare-const (par (T) (setEmpty<T> (Set<T>))))";

        // Heap/Arrays
        FIELD_INST.smt = "(declare-sort Field 2)";

        HEAP_INST.smt = "(declare-sort Heap 0)";
        TYPE_INST.smt = "(declare-sort Type)";
        // OBJECT_INST.smt = "(declare-sort Object)";
        // ARR_1_INST.smt = "(declare-sort (par (T) (ArrT)))";
        // ARR_2_INST.smt = "(declare-sort (par (T) (Arr2T)))";
        TYPE_CONST.smt = "(declare-const (par (C) (Type.C Type)))";

        /**
         * Functions
         */

        // sets
        SETIN.smt = "(declare-fun (par (T)(setin<T> (T Set<T>) Bool)))";
        SETADD.smt = "(declare-fun (par (T)(setadd<T> (T Set<T>) Set<T>)))";
        SETCARD.smt = "(declare-fun (par (T)(setcard<T> (Set<T>) Int)))";
        SETMINUS.smt = "(declare-fun (par (T)(setminus<T> (Set<T> Set<T>) Set<T>)))";
        SETUNION.smt = "(declare-fun (par (T)(setunion<T> (Set<T> Set<T>) Set<T>)))";
        SETINTERSECT.smt = "(declare-fun (par (T)(setintersect<T> (Set<T> Set<T>) Set<T>)))";
        SETSUBSET.smt = "(declare-fun (par (T)(setsubset<T> (Set<T> Set<T>) Bool)))";

        // multisets
        MULTISET_UNION.smt = "(declare-fun (par (T) (munion<T> ((MultiSet<T>) (MultiSet<T>)) (MultiSet<T>))))";
        MULTISET_INTERSECT.smt = "(declare-fun (par (T) (mintersect<T> ((MultiSet<T>) (MultiSet<T>)) (MultiSet<T>))))";
        MULTISET_MINUS.smt = "(declare-fun (par (T) (msetminus<T> ((MultiSet<T>) (MultiSet<T>)) (MultiSet<T>))))";
        MULTISET_CARD.smt = "(declare-fun (par (T) (mcard<T> ((MultiSetT)) Int)))";
        MULTISET_SUBSET.smt = "(declare-fun (par (T) (msubset<T> ((MultiSet<T>) (MultiSet<T>)) Bool)))";
        MULTISET_INSERT.smt = "(declare-fun (par (T) (msetinsert<T>  (T (MultiSet<T>)) (MultiSet<T>))))";
        MULTISET_SELECT.smt = "(declare-fun (par (T) (msetselect<T> ((MultiSet<T>) T) Int)))";
        MULTISET_IN.smt = "(define-fun (par (T) (inmset<T> ((s (MultiSet<T>))  (t T)) Bool\r\n"
                + "(> (msetselect<T> s t) 0)\r\n" + ")))";
        MULTISET_SINGLE.smt = "(define-fun (par (T) (setsingle<T> ((t T) (s (MultiSet<T>))) (MultiSet<T>)\r\n"
                + "(msetinsert<T> t msetEmpty<T>)\r\n" + ")))";
        MULTISET_MAX.smt = "(define-fun max ((x Int) (y Int)) Int\r\n" + "  (ite (<= x y) y x))";
        MULTISET_MIN.smt = "(define-fun min ((x Int) (y Int)) Int\r\n" + "  (ite (<= x y) x y))";

        // sequences
        SEQLEN.smt = "(declare-fun (par (T) (seqlen<T> (Seq<T>) Int)))";
        SEQGET.smt = "(declare-fun (par (T) (seqget<T> (Seq<T> Int) T)))";
        SEQUPD.smt = "(declare-fun (par (T) (sequpd<T> (Seq<T> T Int) Seq<T>)))";
        SEQCONS.smt = "(declare-fun (par (T) (seqcons<T> (T Seq<T>) Seq<T>)))";
        SEQSUBSELECT.smt = "(declare-fun (par (T) (seqsubselect<T> (Seq<T> Int Int) Seq<T>)))";
        SEQCONCAT.smt = "(declare-fun (par (T) (seqconcat<T> (Seq<T> Seq<T>) Seq<T>)))";

        // Heap/Arrays
        O2C.smt = "(declare-fun (par (C) (o2C (Object) C)))";
        C2O.smt = "(declare-fun (par (C) (C2o (C) Object)))";
        TYPEOF.smt = "(declare-fun typeOf (Object) Type)";
        FIELDSTORE.smt = "(declare-fun (par (C T) (fieldstore<C.T> (Heap C (Field<C.T>) T) Heap)))";
        FIELDSELECT.smt = "(declare-fun (par (C T) (fieldselect<C.T> (Heap C (Field<C.T>)) T)))";
        ANON.smt = "(declare-fun anon (Heap (Set<Object>) Heap) Heap)";
        // ANON.smt = "(declare-fun (par (T) (anon ((ArrT)) Int)))";
        CREATE.smt = "(declare-fun create  (Heap Object) Heap)";
        CREATED.smt = "(declare-fun isCreated  (Heap Object) Bool)";
        MODH.smt = "(declare-const modh SetObject)";
        EVERYTHING.smt = "(assert (forall ((o Object)) (setin<Object> o " + Names.getPrefix() + "everything)))";
        EVERYTHING.dependencies = new HashSet<>(Arrays.asList(Axiom.SETIN, Axiom.SETADD)); // SETADD ?
        ARRSELECT.smt = "(declare-fun (par (T) (arrselect<T> (Heap Arr<T> Int) T)))";
        ARRSTORE.smt = "(declare-fun (par (T) (arrstore<T> (Heap (Arr<T>) Int T) Heap)))";
        ARRLEN.smt = "(declare-fun (par (T)(arrlen<T> (Arr<T>) Int)))";
        ARR2SELECT.smt = "(declare-fun (par (T) (arr2select<T> (Heap (Arr2<T>) Int Int) T)))";
        ARR2STORE.smt = "(declare-fun (par (T) (arr2store<T> (Heap (Arr2<T>) Int Int T) Heap)))";
        ARR2LEN0.smt = "(declare-fun (par (T) (arr2len0<T>  ((Arr2<T>)) Int)))";
        ARR2LEN1.smt = "(declare-fun (par (T) (arr2len1<T> ((Arr2<T>)) Int)))";

        /**
         * Axioms
         */

        // sets
        S1.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (t T)\r\n" + ")\r\n" + "(!  \r\n"
                + "(not (setin<T> t ~setempty<T>)) \r\n" + ":pattern((setin<T> t ~setempty<T>))))))";
        S1.dependencies = new HashSet<>(Arrays.asList(Axiom.SETIN));
        S2.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (s Set<T>)\r\n" + "    (x T)\r\n" + "    (y T)\r\n"
                + ")\r\n" + "(! \r\n" + "(= (setin<T> y (setadd<T> x s)) (or (= x y) (setin<T> y s)))\r\n"
                + ":pattern((setin<T> y s) (setadd<T> x s))))))";
        S2.dependencies = new HashSet<>(Arrays.asList(Axiom.SETIN, Axiom.SETADD));
        S3.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "(s1 Set<T>)\r\n" + "(s2 Set<T>)\r\n" + ")\r\n"
                + "(=>  \r\n" + "(forall \r\n" + "(\r\n" + "    (t T)\r\n" + ")\r\n"
                + "(= (setin<T> t s1) (setin<T> t s2))) (= s1 s2)))))";
        S3.dependencies = new HashSet<>(Arrays.asList(Axiom.SETIN));
        S4.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (s1 Set<T>)\r\n" + "    (s2 Set<T>)\r\n"
                + "    (x T)\r\n" + ")\r\n" + "(! \r\n"
                + "(= (setin<T> x (setunion<T> s1 s2)) (or (setin<T> x s1) (setin<T> x s2)))\r\n"
                + ":pattern((setunion<T> s1 s2) (setin<T> x s1))))))";
        S4.dependencies = new HashSet<>(Arrays.asList(Axiom.SETIN, Axiom.SETUNION));
        S5.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (s1 Set<T>)\r\n" + "    (s2 Set<T>)\r\n"
                + "    (x T)\r\n" + ")\r\n" + "(! \r\n"
                + "(= (setin<T> x (setintersect<T> s1 s2)) (and (setin<T> x s1) (setin<T> x s2)))\r\n"
                + ":pattern((setintersect<T> s1 s2) (setin<T> x s1))))))";
        S5.dependencies = new HashSet<>(Arrays.asList(Axiom.SETIN, Axiom.SETINTERSECT));
        S6.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (s1 Set<T>)\r\n" + "    (s2 Set<T>)\r\n"
                + "    (x T)\r\n" + ")\r\n" + "(!\r\n"
                + "(= (setin<T> x (setminus<T> s1 s2)) (and (setin<T> x s1) (not (setin<T> x s2))))\r\n"
                + ":pattern((setminus<T> s1 s2) (setin<T> x s1))))))";
        S6.dependencies = new HashSet<>(Arrays.asList(Axiom.SETIN, Axiom.SETMINUS));
        S7.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "(s1 Set<T>)\r\n" + "(s2 Set<T>)\r\n" + ")\r\n"
                + "(= (setsubset<T> s1 s2) \r\n" + "(forall \r\n" + "(\r\n" + "    (t T)\r\n" + ")\r\n" + "(!\r\n"
                + "(=> (setin<T> t s1) (setin<T> t s2)) \r\n"
                + ":pattern((setsubset<T> s1 s2) (setin<T> t s1) (setin<T> t s2))))))))";
        S7.dependencies = new HashSet<>(Arrays.asList(Axiom.SETIN, Axiom.SETSUBSET));
        SC1.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (s Set<T>)\r\n" + ")\r\n" + "(!\r\n"
                + "(>= (setcard<T> s) 0) \r\n" + ":pattern((setcard<T> s))))))";
        SC1.dependencies = new HashSet<>(Arrays.asList(Axiom.SETCARD));
        SC2.smt = "(assert (par (T) (= (setcard<T> ~setempty<T>) 0)))";
        SC2.dependencies = new HashSet<>(Arrays.asList(Axiom.SETCARD));
        SC3.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (s Set<T>)\r\n" + "    (t T)\r\n" + ")\r\n" + "(!\r\n"
                + "(= (setcard<T> (setadd<T> t s)) (ite (setin<T> t s) (setcard<T> s) (+ (setcard<T> s) 1)))\r\n"
                + ":pattern((setadd<T> t s))))))";
        SC3.dependencies = new HashSet<>(Arrays.asList(Axiom.SETCARD, Axiom.SETADD, Axiom.SETIN));
        // multisets
        MULTISET_1.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s1 (MultiSetT))\r\n" + "    (t T)\r\n"
                + ")\r\n" + "    (! \r\n" + "        (>= (msetselectT s1 t) 0)\r\n"
                + "         :pattern((msetselectT s1 t))\r\n" + "    ) \r\n" + ")))";
        MULTISET_2.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (t T)\r\n" + ")\r\n" + "    (! \r\n"
                + "        (= (msetselectT msetEmptyT t) 0)\r\n" + "         :pattern((msetselectT msetEmptyT t))\r\n"
                + "    ) \r\n" + ")))";
        MULTISET_3.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s1 (MultiSetT))\r\n"
                + "    (s2 (MultiSetT))\r\n" + "    (t T)\r\n" + ")\r\n" + "    (! \r\n"
                + "        (= (msetselectT (mintersectT s1 s2) t)\r\n"
                + "        (min (msetselectT s1 t) (msetselectT s2 t))\r\n"
                + "        ) :pattern((msetselectT s1 t) (msetselectT s2 t))\r\n" + "    ) \r\n" + ")))";
        MULTISET_4.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s1 (MultiSetT))\r\n"
                + "    (s2 (MultiSetT))\r\n" + "    (t T)\r\n" + ")\r\n" + "    (! \r\n"
                + "        (= (msetselectT (munionT s1 s2) t)\r\n"
                + "        (+ (msetselectT s1 t) (msetselectT s2 t))) \r\n"
                + "        :pattern((msetselectT s1 t) (msetselectT s2 t))\r\n" + "    ) \r\n" + ")))";
        MULTISET_5.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s1 (MultiSetT))\r\n"
                + "    (s2 (MultiSetT))\r\n" + "    (t T)\r\n" + ")\r\n" + "    (! \r\n"
                + "        (= (msetselectT (msetminusT s1 s2) t)\r\n"
                + "            (max (- (msetselectT s1 t)  (msetselectT s2 t))  0)\r\n" + "        )\r\n"
                + "        :pattern ((msetselectT s1 t) (msetselectT s2 t))\r\n" + "    ) \r\n" + ")))";
        MULTISET_6.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s1 (MultiSetT))\r\n"
                + "    (s2 (MultiSetT))\r\n" + "    (t T)\r\n" + ")\r\n" + "    (!\r\n"
                + "        (= (msubsetT s1 s2)\r\n" + "        (<=  (msetselectT s1 t) (msetselectT s2 t))\r\n"
                + "        ):pattern ((msetselectT s1 t) (msetselectT s2 t))\r\n" + "    )\r\n" + ")))";
        MULTISET_7.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s (MultiSetT))\r\n" + "    (t T)\r\n"
                + ")\r\n" + "    (!\r\n"
                + "        (= (msetselectT (msetinsertT t s) t) (+ (msetselectT s t) 1)) :pattern((msetinsertT t s))\r\n"
                + "    )\r\n" + "     \r\n" + ")))";
        MULTISET_8.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s (MultiSetT))\r\n" + ")\r\n"
                + "    (! \r\n" + "        (=> (= (mcardT s) 0)\r\n" + "        (= s msetEmptyT)) \r\n"
                + "        :pattern ((mcardT s))\r\n" + "    ) \r\n" + ")))";
        MULTISET_CARD_1.smt = "(assert (par (T) (= (mcardT msetEmptyT) 0)))";
        MULTISET_CARD_2.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s (MultiSetT))\r\n" + ")\r\n"
                + "    (! \r\n" + "        (>=  (mcardT s) 0) \r\n" + "        :pattern ((mcardT s))\r\n" + "    ) \r\n"
                + ")))";
        MULTISET_CARD_3.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s1 (MultiSetT))\r\n"
                + "    (s2 (MultiSetT))\r\n" + ")\r\n" + "    (! \r\n" + "        (=> (msubsetT s1 s2)\r\n"
                + "        (<= (mcardT s1) (mcardT s2))) \r\n" + "        :pattern ((msubsetT s1 s2))\r\n"
                + "    ) \r\n" + ")))";
        MULTISET_CARD_4.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s (MultiSetT))\r\n"
                + "    (t T)\r\n" + ")\r\n" + "    (! \r\n"
                + "        (= (mcardT (msetinsertT t s))  (+ (mcardT s) 1))\r\n"
                + "        :pattern ((msetinsertT t s))\r\n" + "    ) \r\n" + ")))";

        // sequences
        SQ1.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (i Int)\r\n" + "    (j Int)\r\n"
                + "    (s Seq<T>)\r\n" + "    (t T)\r\n" + ")\r\n"
                + "(= (seqget<T> (sequpd<T> s t i) j) (ite (= i j) t (seqget<T> s j))))))";
        SQ1.dependencies = new HashSet<>(Arrays.asList(Axiom.SEQGET,  Axiom.SEQUPD));
        SQ2.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (i Int)\r\n" + "    (s Seq<T>)\r\n" + "    (t T)\r\n"
                + ")\r\n" + "(= (seqget<T> (seqcons<T> t s) i) (ite  (= i 0) t (seqget<T> s (- i 1)))))))";
        SQ2.dependencies = new HashSet<>(Arrays.asList(Axiom.SEQGET, Axiom.SEQCONS));
        SQ3.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (i Int)\r\n" + "    (s1 Seq<T>)\r\n"
                + "    (s2 Seq<T>)\r\n" + ")\r\n" + "(!\r\n"
                + "(= (seqget<T> (seqconcat<T> s1 s2) i) (ite (< i (seqlen<T> s1)) (seqget<T> s1 i) (seqget<T> s2 (- i (seqlen<T> s1)\r\n"
                + ")))\r\n" + ") :pattern((seqconcat<T> s1 s2) (seqget<T> s1 i))))))";
        SQ3.dependencies = new HashSet<>(Arrays.asList(Axiom.SEQGET, Axiom.SEQLEN, Axiom.SEQCONCAT));
        SQ4.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (i Int)\r\n" + "    (j Int)\r\n" + "    (k Int)\r\n"
                + "    (s Seq<T>)\r\n" + ")\r\n" + "(!\r\n"
                + "(= (seqget<T> (seqsubselect<T> s i j) k) (seqget<T> s (+ i k))) :pattern ((seqsubselect<T> s i j) (seqget<T> s k))))))";
        SQ4.dependencies = new HashSet<>(Arrays.asList(Axiom.SEQGET, Axiom.SEQSUBSELECT));
        SQ5.smt = "(assert (par (T) (forall \r\n" + "(\r\n" + "    (i Int)\r\n" + "    (s1 Seq<T>)\r\n"
                + "    (s2 Seq<T>)\r\n" + ")\r\n" + "(!\r\n" + "(=>  \r\n"
                + "(and (= (seqlen<T> s1) (seqlen<T> s2)) (= (seqget<T> s1 i) (seqget<T> s2 i)))\r\n"
                + "(= s1 s2)) :pattern((seqget<T> s1 i) (seqget<T> s2 i))))))";
        SQ5.dependencies = new HashSet<>(Arrays.asList(Axiom.SEQGET, Axiom.SEQLEN));
        SQ6.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (s Seq<T>)\r\n" + ")\r\n" + "(=>   \r\n"
                + "(= (seqlen<T> s) 0)\r\n" + "(= s ~seqempty<T>)))))";
        SQ6.dependencies = new HashSet<>(Arrays.asList(Axiom.SEQLEN));
        SQL1.smt = "(assert (par (T) (= (seqlen<T> ~seqempty<T>) 0)))";
        SQL1.dependencies = new HashSet<>(Arrays.asList(Axiom.SEQLEN));
        SQL2.smt = "(assert (par (T) (forall   \r\n" + "(\r\n" + "    (s Seq<T>)\r\n" + ")\r\n"
                + "(>= (seqlen<T> s) 0)\r\n" + ")))";
        SQL2.dependencies = new HashSet<>(Arrays.asList(Axiom.SEQLEN));
        SQL3.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (i Int)\r\n" + "    (j Int)\r\n"
                + "    (s Seq<T>)\r\n" + ")\r\n" + "(!\r\n" + "(= (seqlen<T> (seqsubselect<T> s i j)) (- j i))\r\n"
                + ") :pattern((seqsubselect<T> s i j)))))";
        SQL3.dependencies = new HashSet<>(Arrays.asList(Axiom.SEQLEN, Axiom.SEQSUBSELECT));
        SQL4.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (s1 Seq<T>)\r\n" + "    (s2 Seq<T>)\r\n" + ")\r\n"
                + "(!\r\n"
                + "(= (seqlen<T> (seqconcat<T> s1 s2))  (+ (seqlen<T> s1) (seqlen<T> s2))) :pattern((seqconcat<T> s1 s2))))))";
        SQL4.dependencies = new HashSet<>(Arrays.asList(Axiom.SEQLEN, Axiom.SEQCONCAT));
        SQL5.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (s Seq<T>)\r\n" + "    (t T)\r\n" + ")\r\n"
                + "(!\r\n" + "(= (seqlen<T> (seqcons<T> t s)) (+ (seqlen<T> s) 1)) :pattern((seqcons<T> t s))))))";
        SQL5.dependencies = new HashSet<>(Arrays.asList(Axiom.SEQLEN, Axiom.SEQCONS));

        // Heap/Arrays
        ARR_1.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (i Int)\r\n" + "    (h Heap)\r\n"
                + "    (a (Arr<T>))\r\n" + "    (v T)\r\n" + ")\r\n" + "(!\r\n"
                + "    (= (arrselect<T> (arrstore<T> h a i v) a i) v) :pattern((arrstore<T> h a i v))\r\n" + "))))";
        ARR_2.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (a (Arr<T>))\r\n" + ")\r\n" + "(!\r\n"
                + "    (> (arrlen<T> a) 0) :pattern((arrlen<T> a))\r\n" + "))))";
        ARR2_1.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (i Int)\r\n" + "    (j Int)\r\n"
                + "    (h Heap)\r\n" + "    (a (Arr2<T>))\r\n" + "    (v T)\r\n" + ")\r\n" + "(!\r\n"
                + "    (= (arr2select<T> (arr2store<T> h a i j v) a i j) v) :pattern((arr2store<T> h a i j v) )\r\n"
                + "))))";
        HEAP_1.smt = "(assert (par (C T) (forall\r\n" + "(\r\n" + "    (v T)\r\n" + "    (h Heap)\r\n" + "    (c C)\r\n"
                + "    (f (Field<C.T>))\r\n" + "\r\n" + ")\r\n" + "(!\r\n" + "  \r\n"
                + "    (= (fieldselect<C.T> (fieldstore<C.T> h c f v) c f) v) :pattern((fieldstore<C.T> h c f v))\r\n"
                + "))))";
        HEAP_2.smt = "(assert (par (C T) (forall\r\n" + "(\r\n" + "    (v T)\r\n" + "    (h Heap)\r\n"
                + "    (c1 C)\r\n" + "    (c2 C)\r\n" + "    (f1 (Field<C.T>))\r\n" + "    (f2 (Field<C.T>))\r\n"
                + "\r\n" + ")\r\n" + "(!\r\n" + "    (=> (or (distinct c1 c2) (distinct f1 f2))\r\n"
                + "    (= (fieldselect<C.T> (fieldstore<C.T> h c1 f1 v) c2 f2) (fieldselect<C.T> h c2 f2)))\r\n"
                + "     :pattern((fieldstore<C.T> h c1 f1 v) (fieldstore<C.T> h c2 f2 v))\r\n" + "))))";
        HEAP_3.smt = "(assert (forall\r\n" + "(\r\n" + "    (h Heap)\r\n" + "    (o Object)\r\n" + "\r\n" + ")\r\n"
                + "(!\r\n" + "    (= (isCreated (create h o) o ) true) :pattern((create h o))\r\n" + ")))";
        HEAP_4.smt = "(assert (par (C T) (forall\r\n" + "(\r\n" + "    (c C)\r\n" + "    (h1 Heap)\r\n"
                + "    (h2 Heap)\r\n" + "    (s (Set Object))\r\n" + "    (f (Field<C.T>))\r\n" + ")\r\n" + "(! \r\n"
                + "    (= (fieldselect<C.T> (anon h1 s h2) c f) (fieldselect<C.T> (ite (select s (c2o c)) h2 h1) c f)) :pattern((anon h1 s h2) (fieldselect<C.T> h1 c f))    \r\n"
                + "))))";
        HEAP_5.smt = "(assert (par (C) (forall ((c C)) (! (= (o2c (c2o c)) c) :pattern ((o2c (c2o c)))))))\r\n";
        HEAP_6.smt = "(assert (par (C) (forall ((o Object)) (=> (= (typeOf o) Type.C) (= (c2o (o2c o)) o)))))";

    }

    private Set<Axiom> dependencies = new HashSet<>();

    private String smt;

    public String getSmt() {
        return smt;
    }

    public Set<Axiom> getDependencies() {
        return dependencies;
    }

}