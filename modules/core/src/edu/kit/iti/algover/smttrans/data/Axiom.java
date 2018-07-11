package edu.kit.iti.algover.smttrans.data;

import edu.kit.iti.algover.smttrans.translate.Names;

public enum Axiom {

    /**
     * Sorts
     */

    // sets
    // SET_INST,
    SETEMPTY_INST,

    // multisets
    MULTISET_INST, MULTISETEMTPY_INST,

    // sequences
    SEQ_INST, SEQEMTY_INST,

    // Heap/Arrays
    FIELD_INST, HEAP_INST, TYPE_INST, OBJECT_INST, // ARR_1_INST, //ARR_2_INST
    TYPE_CONST, EVERYTHING,

    /**
     * Functions
     */

    // sets
    SET_UNION, SET_INTERSECT, SET_MINUS, SET_CARD, SET_SUBSET, SET_SINGLE, SET_INSERT, SET_SELECT, SET_IN,

    // multisets
    MULTISET_UNION, MULTISET_INTERSECT, MULTISET_MINUS, MULTISET_CARD, MULTISET_SUBSET, MULTISET_INSERT, MULTISET_SELECT, MULTISET_IN, MULTISET_SINGLE, MULTISET_MAX, MULTISET_MIN,

    // sequences
    SEQ_GET, SEQ_SUBSELECT, SEQ_CONCAT, SEQ_APPEND, SEQ_LEN, SEQ_SINGLE, SEQ_STORE, SEQ_CONS,

    // Heap/Arrays
    O2C, C2O, FIELDSTORE, FIELDSELECT, ANON, CREATE, CREATED, MODH, ARRSELECT, ARR2SELECT, ARR2STORE, ARR2LEN0, ARR2LEN1, ARRLEN, ARRSTORE, TYPEOF,

    /**
     * Axioms
     */

    // sets
    SET_1, SET_2, SET_3, SET_4, SET_5, SET_6, SET_7, SET_8, SET_CARD_1, SET_CARD_2, SET_CARD_3, SET_CARD_4, SET_0,

    // multisets
    MULTISET_1, MULTISET_2, MULTISET_3, MULTISET_4, MULTISET_5, MULTISET_6, MULTISET_7, MULTISET_8, MULTISET_CARD_1, MULTISET_CARD_2, MULTISET_CARD_3, MULTISET_CARD_4,

    // sequences
    SEQ_0, SEQ_1, SEQ_2, SEQ_3, SEQ_4, SEQ_5, SEQ_6, SEQ_LEN_1, SEQ_LEN_2, SEQ_LEN_3, SEQ_LEN_4, SEQ_LEN_5,

    // Heap/Arrays
    ARR_1, ARR_2, ARR2_1, HEAP_1, HEAP_2, HEAP_3, HEAP_4, HEAP_5, HEAP_6, SEQ_7;

    static {

        /**
         * Sorts
         */

        // sets
        // SET_INST.smt = "(define-sort Set (T) (Array T Bool))"; //TODO
        SETEMPTY_INST.smt = "(declare-const (par (T) (setEmpty<T> (Set<T>))))";

        // multisets
        MULTISET_INST.smt = "(declare-sort MultiSet 1)";
        MULTISETEMTPY_INST.smt = "(declare-const (par (T) (msetEmptyT (MultiSetT))))";

        // sequences
        SEQ_INST.smt = "(declare-sort Seq 1)";
        SEQEMTY_INST.smt = "(declare-const (par (T) (emtpyseq<T> Seq<T>)))";

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
        SET_UNION.smt = "(declare-fun (par (T) (union<T> (Set<T> Set<T>) (Set<T>))))";
        SET_INTERSECT.smt = "(declare-fun (par (T) (intersect<T> (Set<T> Set<T>) (Set<T>))))";
        SET_MINUS.smt = "(declare-fun (par (T) (setminus<T> (Set<T> Set<T>) (Set<T>))))";
        SET_CARD.smt = "(declare-fun (par (T) (setcard<T> (Set<T>) Int)))";
        SET_SUBSET.smt = "(declare-fun (par (T) (subset<T> (Set<T> Set<T>) Bool)))";
        SET_SINGLE.smt = "(define-fun  (par (T) (setsingle<T> ((t T) (s (Set<T>))) (Set<T>)))\r\n"
                + "(store setEmpty<T> t true)\r\n" + ")";
        SET_INSERT.smt = "(declare-fun (par (T) (setInsert<T> (T (Set<T>)) (Set<T>))))";
        SET_SELECT.smt = "";
        SET_IN.smt = "(declare-fun (par (T) (inSet<T> (T (Set<T>)) Bool)))";

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
        SEQ_GET.smt = "(declare-fun (par (T)(seqget<T>((Seq<T>) Int) T)))";
        SEQ_STORE.smt = "(declare-fun (par (T)(seqstore<T>((Seq<T>) Int T) (Seq<T>))))";
        SEQ_SUBSELECT.smt = "(declare-fun (par (T)(subseqselect<T> ((Seq<T>) Int Int) (Seq<T>))))";
        SEQ_CONCAT.smt = "(declare-fun (par (T)(seqconcat<T> ((Seq<T>) (Seq<T>)) (Seq<T>))))";
        SEQ_APPEND.smt = "(declare-fun (par (T)(seqappend<T> ((Seq<T>) T) (Seq<T>))))";
        SEQ_LEN.smt = "(declare-fun (par (T)(seqlen<T> ((Seq<T>)) Int)))";
        SEQ_CONS.smt = "(declare-fun (par (T)(seqcons<T> (T (Seq<T>)) (Seq<T>))))";
        SEQ_SINGLE.smt = "(define-fun (par (T) (seqsingle<T> ((t T))  (Seq<T>)  \r\n"
                + "(seqappend<T> emtpyseq<T> t)\r\n" + ")))";

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
        EVERYTHING.smt = "(assert (forall ((o Object)) (inSet<Object> o " + Names.getPrefix() + "everything)))";
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

        SET_0.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (t T)\r\n" + ") \r\n"
                + "        (not (inSet<T> t ~setEmpty<T>))      \r\n" + ")))";
        SET_1.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s1 Set<T>)\r\n" + "    (t T)\r\n" + ")\r\n"
                + "    (! \r\n" + "        (= (inSet<T> t (setInsert<T> t s1)) true) \r\n"
                + "        :pattern ((inSet<T> t (setInsert<T> t s1)))\r\n" + "    ) \r\n" + ")))";

        SET_2.smt = "(assert (par (T) (forall ((a (Set<T>)) (i T) (j T))\r\n" + "      (=> (distinct i j)\r\n"
                + "               (= (inSet<T> j (setInsert<T> i a )) (inSet<T>  j a))))))";

        SET_3.smt = "(assert (par (T) (forall ((a (Set<T>)) (b (Set<T>)))\r\n" // TODO timeout, needed ?
                + "      (=> (forall ((i T)) (= (inSet<T> i a) (inSet<T> i b)))\r\n" + "(= a b)))))";
        SET_4.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s1 Set<T>)\r\n" + "    (s2 Set<T>)\r\n"
                + "    (t T)\r\n" + ")\r\n" + "    (! \r\n" + "        (= (inSet<T> t (union<T> s1 s2))\r\n"
                + "        (or (inSet<T> t s1) (inSet<T> t s2))) \r\n"
                + "        :pattern (( inSet<T> t (union<T> s1 s2)))\r\n" + "    ) \r\n" + ")))";
        SET_5.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s1 Set<T>)\r\n" + "    (s2 Set<T>)\r\n"
                + "    (t T)\r\n" + ")\r\n" + "    (! \r\n" + "        (= (inSet<T> t (intersect<T> s1 s2))\r\n"
                + "        (and (inSet<T> t s1) (inSet<T> t s2))) \r\n"
                + "        :pattern ((inSet<T> t (intersect<T> s1 s2)))\r\n" + "    ) \r\n" + ")))";
        SET_6.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s1 Set<T>)\r\n" + "    (s2 Set<T>)\r\n"
                + "    (t T)\r\n" + ")\r\n" + "    (! \r\n" + "        (= (inSet<T> t (setminus<T> s1 s2))\r\n"
                + "        (and (inSet<T> t s1) (not (inSet<T> t s2)))) \r\n"
                + "        :pattern ((inSet<T> t (setminus<T> s1 s2)))\r\n" + "    ) \r\n" + ")))";
        SET_7.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s1 Set<T>)\r\n" + "    (s2 Set<T>)\r\n"
                + "    (t T)\r\n" + ")\r\n" + "    (! \r\n" + "        (= (subset<T> s1 s2)\r\n"
                + "        (=> (inSet<T> t s1) (inSet<T> t s2))) \r\n"
                + "        :pattern ((subset s1 s2) (inSet<T> t s1))\r\n" + "    ) \r\n" + ")))";
        SET_8.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s Set<T>)\r\n" + ")\r\n" + "    (! \r\n"
                + "        (=> (= (setcard<T> s) 0)\r\n" + "        (= s ~setEmpty<T>)) \r\n"
                + "        :pattern ((setcard<T> s))\r\n" + "    ) \r\n" + ")))";
        SET_CARD_1.smt = "(assert (par (T) (= (setcard<T> ~setEmpty<T>) 0)))";
        SET_CARD_2.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s (Set<T>))\r\n" + ")\r\n"
                + "    (! \r\n" + "        (>=  (setcard<T> s) 0) \r\n" + "        :pattern ((setcard<T> s))\r\n"
                + "    ) \r\n" + ")))";
        SET_CARD_3.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s1 (Set<T>))\r\n"
                + "    (s2 (Set<T>))\r\n" + ")\r\n" + "    (! \r\n" + "        (=> (subset<T> s1 s2)\r\n"
                + "        (<= (setcard<T> s1) (setcard<T> s2))  \r\n" + "        ) \r\n"
                + "        :pattern ((setcard<T> s))\r\n" + "    ) \r\n" + ")))";
        SET_CARD_4.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s (Set<T>))\r\n" + "    (t T)\r\n"
                + ")\r\n" + "    (! \r\n"
                + "        (= (setcard<T> (setInsert<T> t s))  (ite (inSet<T> t s)  (setcard<T> s) (+ (setcard<T> s) 1) )) \r\n"
                + "        :pattern ((setcard<T>(setInsert<T> t s)) (inSet<T> t s))\r\n" + "    ) \r\n" + ")))";

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
        SEQ_0.smt = "(assert  (par (T) (forall\r\n" + "(\r\n" + " (s1 (Seq<T>))\r\n" + " (i Int)\r\n" + "    (t T)\r\n"
                + ")\r\n" + "    (!\r\n"
                + "    (= (seqget<T> (seqstore<T> s1 i t) i)t) :pattern((seqstore<T> s1 i t))\r\n" + "))))";
        SEQ_1.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (s (Seq<T>))\r\n" + "    (t T)\r\n"
                + "    (i Int)\r\n" + ")\r\n" + "    (!\r\n" + "    (=> (and  (>= i 0) (<= i (seqlen<T> s))  )\r\n"
                + "    (= (seqget<T> (seqappend<T> s t) i) (ite (= i (- (seqlen<T> s) 1) )  t  (seqget<T> s i) )\r\n"
                + "    )):pattern ((seqappend<T> s t) (seqget<T> s i))\r\n" + "      )\r\n" + ")))";
        SEQ_2.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (s1 (Seq<T>))\r\n" + "    (s2 (Seq<T>))\r\n"
                + "    (i Int)\r\n" + ")\r\n" + "    (!\r\n"
                + "    (=>  (and (>= i 0) (<= i (- (+ (seqlen<T> s1) (seqlen<T> s2)) 2)  ) )\r\n"
                + "    (= (seqget<T> (seqconcat<T> s1 s2) i)   (ite (< (seqlen<T> s1) i)  (seqget<T> s1 i) (seqget<T> s2 i) )\r\n"
                + "      )):pattern ((seqconcat<T> s1 s2) (seqget<T> s1 i))\r\n" + "      )\r\n" + ")))";
        SEQ_3.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (s (Seq<T>))\r\n" + "    (i Int)\r\n"
                + "    (j Int)\r\n" + "    (k Int)\r\n" + ")\r\n" + "    (! \r\n"
                + "    (=> (and (<= 0 i k j) (< j (seqlen<T> s)) )\r\n"
                + "    (= (seqget<T> (subseqselect<T> s i j) k)   (seqget<T> s (+ i k)) \r\n"
                + "      )):pattern ((subseqselect<T> s i j) (seqget<T> s k))\r\n" + "      )\r\n" + ")))";
        SEQ_4.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (s1 (Seq<T>))\r\n" + "    (s2 (Seq<T>))\r\n"
                + ")\r\n" + "    (! \r\n" + "    (=>\r\n" + "    (and (= (seqlen<T> s1) (seqlen<T> s2))\r\n"
                + "    (forall\r\n" + "    ((i Int))\r\n" + "    (!   \r\n"
                + "    (=> (and (>= 0 i) (< i (seqlen<T> s1)))\r\n"
                + "    (= (seqget<T> s1 i)(seqget<T> s2 i))) :pattern((seqget<T> s1 i) (seqget<T> s2 i))\r\n"
                + "    )))\r\n" + "    (= s1 s2)\r\n" + "    ) :pattern((seqlen<T> s1) (seqlen<T> s2))\r\n" + "))))";
        SEQ_5.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (s (Seq<T>))\r\n" + ")\r\n" + "    (! \r\n"
                + "    (=>  (= (seqlen<T> s) 0) \r\n" + "    (= s emtpyseq<T>)\r\n"
                + "    ):pattern ((seqlen<T> s))\r\n" + "    )\r\n" + ")))";

        SEQ_6.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (t T)\r\n" + "    (s1 (Seq<T>))\r\n" + ")\r\n"
                + "\r\n" + "(= (seqlen<T> (seqcons<T> t s1))  (+ (seqlen<T> s1) 1))\r\n" + "\r\n" + ")))";
        
        SEQ_7.smt = "(assert (par (T) (forall\r\n" + 
                "(\r\n" + 
                "    (t T)\r\n" + 
                "    (s1 (Seq<T>))\r\n" + 
                ")\r\n" + 
                " \r\n" + 
                " (forall \r\n" + 
                " (\r\n" + 
                "    (i Int)\r\n" + 
                " ) \r\n" + 
                "    (= (seqget<T> (seqcons<T> t s1) i)  (ite (= i 0) t (seqget<T> s1 (+ i 1))))  \r\n" + 
                "))))";

        SEQ_LEN_1.smt = "(assert (par (T) (= (seqlen<T> emtpyseq<T>) 0)))";
        SEQ_LEN_2.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (s (Seq<T>))\r\n" + ")\r\n" + "    (! \r\n"
                + "    (>= (seqlen<T> s) 0):pattern((seqlen<T> s))\r\n" + "    ) \r\n" + ")))";
        SEQ_LEN_3.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (s (Seq<T>))\r\n" + "    (t T)\r\n" + ")\r\n"
                + "    (! \r\n"
                + "    (= (seqlen<T> (seqappend<T> s t)) (+ (seqlen<T> s) 1)) :pattern((seqappend<T> s t))\r\n"
                + "    ) \r\n" + ")))";
        SEQ_LEN_4.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (s (Seq<T>))\r\n" + "    (i Int)\r\n"
                + "    (j Int)\r\n" + ")\r\n" + "    (!\r\n" + "    (=>  (<= i j)\r\n"
                + "    (= (seqlen<T> (subseqselect<T> s i j)) (+ (- j i) 1))) :pattern((subseqselect<T> s i j))\r\n"
                + "    )\r\n" + ")))";
        SEQ_LEN_5.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (s1 (Seq<T>))\r\n" + "    (s2 (Seq<T>))\r\n"
                + ")\r\n" + "    (! \r\n"
                + "    (= (seqlen<T> (seqconcat<T> s1 s2)) (+ (seqlen<T> s1) (seqlen<T> s2))) :pattern((seqconcat<T> s1 s2))\r\n"
                + "    ) \r\n" + ")))";

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

    private String smt;

    public String getSmt() {
        return smt;
    }

}