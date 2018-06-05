package edu.kit.iti.algover.smttrans.data;

public enum Axiom {

    /**
     * Sorts
     */

    // sets
    SET_INST, SETEMPTY_INST,

    // multisets
    MULTISET_INST, MULTISETEMTPY_INST,

    // sequences
    SEQ_INST, SEQEMTY_INST,

    // Heap/Arrays
    FIELD_INST, HEAP_INST, TYPE_INST, OBJECT_INST, ARR_1_INST, ARR_2_INST, TYPE_CONST,

    /**
     * Functions
     */

    // sets
    SET_UNION, SET_INTERSECT, SET_MINUS, SET_CARD, SET_SUBSET, SET_SINGLE, SET_INSERT, SET_SELECT, SET_IN,

    // multisets
    MULTISET_UNION, MULTISET_INTERSECT, MULTISET_MINUS, MULTISET_CARD, MULTISET_SUBSET, MULTISET_INSERT, MULTISET_SELECT, MULTISET_IN, MULTISET_SINGLE, MULTISET_MAX, MULTISET_MIN,

    // sequences
    SEQ_GET, SEQ_SUBSELECT, SEQ_CONCAT, SEQ_APPEND, SEQ_LEN, SEQ_SINGLE,

    // Heap/Arrays
    O2C, C2O, FIELDSTORE, FIELDSELECT, ANON, CREATE, CREATED, MODH, ARRSELECT, ARR2SELECT, ARR2STORE, ARR2LEN0, ARR2LEN1, ARRLEN, ARRSTORE, TYPEOF,

    /**
     * Axioms
     */

    // sets
    SET_1, SET_2, SET_3, SET_4, SET_5, SET_CARD_1, SET_CARD_2, SET_CARD_3, SET_CARD_4,

    // multisets
    MULTISET_1, MULTISET_2, MULTISET_3, MULTISET_4, MULTISET_5, MULTISET_6, MULTISET_7, MULTISET_8, MULTISET_CARD_1, MULTISET_CARD_2, MULTISET_CARD_3, MULTISET_CARD_4,

    // sequences
    SEQ_1, SEQ_2, SEQ_3, SEQ_4, SEQ_5, SEQ_LEN_1, SEQ_LEN_2, SEQ_LEN_3, SEQ_LEN_4, SEQ_LEN_5,

    // Heap/Arrays
    ARR_1, ARR2_1, HEAP_1, HEAP_2, HEAP_3, HEAP_4, HEAP_5, HEAP_6;

    static {

        /**
         * Sorts
         */

        // sets
        SET_INST.smt = "(define-sort Set (T) (Array T Bool))";
        SETEMPTY_INST.smt = "(declare-const (par (T) (setEmptyT (Set T))))";

        // multisets
        MULTISET_INST.smt = "(declare-sort MultiSet 1)";
        MULTISETEMTPY_INST.smt = "(declare-const (par (T) (msetEmptyT (MultiSet T))))";

        // sequences
        SEQ_INST.smt = "(declare-sort Seqq 1)";
        SEQEMTY_INST.smt = "(declare-const (par (T) (emtpyseqT (Seqq T))))";

        // Heap/Arrays
        FIELD_INST.smt = "(declare-sort Field 2)";
        HEAP_INST.smt = "(declare-sort Heap)";
        TYPE_INST.smt = "(declare-sort Type)";
        OBJECT_INST.smt = "(declare-sort Object)";
        ARR_1_INST.smt = "(declare-sort Arr 1)";
        ARR_2_INST.smt = "(declare-sort Arr2 1)";
        TYPE_CONST.smt = "(declare-const (par (C) (Type.C Type)))";

        /**
         * Functions
         */

        // sets
        SET_UNION.smt = "(declare-fun (par (T) (unionT ((Set T) (Set T)) (Set T))))";
        SET_INTERSECT.smt = "(declare-fun (par (T) (intersectT ((Set T) (Set T)) (Set T))))";
        SET_MINUS.smt = "(declare-fun (par (T) (setminusT ((Set T) (Set T)) (Set T))))";
        SET_CARD.smt = "(declare-fun (par (T) (cardT ((Set T)) Int)))";
        SET_SUBSET.smt = "(declare-fun (par (T) (subsetT ((Set T) (Set T)) Bool)))";
        SET_SINGLE.smt = "(define-fun  (par (T) (setsingle ((t T) (s (Set T))) (Set T)))\r\n"
                + "(store setEmpty t true)\r\n" + ")";
        SET_INSERT.smt = "";
        SET_SELECT.smt = "";
        SET_IN.smt = "";

        // multisets
        MULTISET_UNION.smt = "(declare-fun (par (T) (munionT ((MultiSet T) (MultiSet T)) (MultiSet T))))";
        MULTISET_INTERSECT.smt = "(declare-fun (par (T) (mintersectT ((MultiSet T) (MultiSet T)) (MultiSet T))))";
        MULTISET_MINUS.smt = "(declare-fun (par (T) (msetminusT ((MultiSet T) (MultiSet T)) (MultiSet T))))";
        MULTISET_CARD.smt = "(declare-fun (par (T) (mcardT ((MultiSet T)) Int)))";
        MULTISET_SUBSET.smt = "(declare-fun (par (T) (msubsetT ((MultiSet T) (MultiSet T)) Bool)))";
        MULTISET_INSERT.smt = "(declare-fun (par (T) (msetinsertT  ((MultiSet T) T) (MultiSet T))))";
        MULTISET_SELECT.smt = "(declare-fun (par (T) (msetselectT ((MultiSet T) T) Int)))";
        MULTISET_IN.smt = "(define-fun (par (T) (inmsetT ((s (MultiSet T))  (t T)) Bool\r\n"
                + "(> (msetselectT s t) 0)\r\n" + ")))";
        MULTISET_SINGLE.smt = "(define-fun (par (T) (setsingleT ((t T) (s (MultiSet T))) (MultiSet T)\r\n"
                + "(msetinsertT msetEmptyT t)\r\n" + ")))";
        MULTISET_MAX.smt = "(define-fun max ((x Int) (y Int)) Int\r\n" + "  (ite (<= x y) y x))";
        MULTISET_MIN.smt = "(define-fun min ((x Int) (y Int)) Int\r\n" + "  (ite (<= x y) x y))";

        // sequences
        SEQ_GET.smt = "(declare-fun (par (T) (seqgetT((Seqq T) Int) T)))";
        SEQ_SUBSELECT.smt = "(declare-fun (par (T) (subseqselectT ((Seqq T) Int Int) (Seqq T))))";
        SEQ_CONCAT.smt = "(declare-fun (par (T) (seqconcatT ((Seqq T) (Seqq T)) (Seqq T))))";
        SEQ_APPEND.smt = "(declare-fun (par (T) (seqappendT ((Seqq T) T) (Seqq T))))";
        SEQ_LEN.smt = "(declare-fun (par (T) (seqlenT ((Seqq T)) Int)))";
        SEQ_SINGLE.smt = "(define-fun (par (T) (seqsingleT ((t T))  (Seqq T)  \r\n" + "(seqappendT emtpyseqT t)\r\n"
                + ")))";

        // Heap/Arrays
        O2C.smt = "(declare-fun (par (C) (o2c (Object) C)))";
        C2O.smt = "(declare-fun (par (C) (c2o (C) Object)))";
        TYPEOF.smt = "(declare-fun typeOf (Object) Type)";
        FIELDSTORE.smt = "(declare-fun (par (C T) (fieldstoreC.T (Heap C (Field C T) T) Heap)))";
        FIELDSELECT.smt = "(declare-fun (par (C T) (fieldselectC.T (Heap C (Field C T)) T)))";
        ANON.smt = "(declare-fun anon (Heap (Set Object) Heap) Heap)";
        CREATE.smt = "(declare-fun create  (Heap Object) Heap)";
        CREATED.smt = "(declare-fun created  (Heap Object) Bool)";
        MODH.smt = "(declare-fun modh (Heap (Set Object)) Heap)";
        ARRSELECT.smt = "(declare-fun (par (T) (arrselectT (Heap (Arr T) Int) T)))";
        ARRSTORE.smt = "(declare-fun (par (T) (arrstoreT (Heap (Arr T) Int T) Heap)))";
        ARRLEN.smt = "(declare-fun (par (T) (arrlenT  ((Arr T)) Int)))";
        ARR2SELECT.smt = "(declare-fun (par (T) (arr2selectT (Heap (Arr2 T) Int Int) T)))";
        ARR2STORE.smt = "(declare-fun (par (T) (arr2storeT (Heap (Arr2 T) Int Int T) Heap)))";
        ARR2LEN0.smt = "(declare-fun (par (T) (arr2Tlen0  ((Arr2 T)) Int)))";
        ARR2LEN1.smt = "(declare-fun (par (T) (arr2Tlen1 ((Arr2 T)) Int)))";

        /**
         * Axioms
         */

        // sets
        SET_1.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s1 (Set T))\r\n" + "    (s2 (Set T))\r\n"
                + "    (t T)\r\n" + ")\r\n" + "    (! \r\n" + "        (= (select (unionT s1 s2) t)\r\n"
                + "        (or (select s1 t) (select s2 t))) \r\n" + "        :pattern (( select (unionT s1 s2) t))\r\n"
                + "    ) \r\n" + ")))";
        SET_2.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s1 (Set T))\r\n" + "    (s2 (Set T))\r\n"
                + "    (t T)\r\n" + ")\r\n" + "    (! \r\n" + "        (= (select (intersectT s1 s2) t)\r\n"
                + "        (and (select s1 t) (select s2 t))) \r\n"
                + "        :pattern ((select (intersectT s1 s2) t))\r\n" + "    ) \r\n" + ")))";
        SET_3.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s1 (Set T))\r\n" + "    (s2 (Set T))\r\n"
                + "    (t T)\r\n" + ")\r\n" + "    (! \r\n" + "        (= (select (setminusT s1 s2) t)\r\n"
                + "        (and (select s1 t) (not (select s2 t)))) \r\n"
                + "        :pattern ((select (setminusT s1 s2) t))\r\n" + "    ) \r\n" + ")))";
        SET_4.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s1 (Set T))\r\n" + "    (s2 (Set T))\r\n"
                + "    (t T)\r\n" + ")\r\n" + "    (! \r\n" + "        (= (subsetT s1 s2)\r\n"
                + "        (=> (select s1 t) (select s2 t))) \r\n"
                + "        :pattern ((subset s1 s2) (select s1 t))\r\n" + "    ) \r\n" + ")))";
        SET_5.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s (Set T))\r\n" + ")\r\n" + "    (! \r\n"
                + "        (=> (= (cardT s) 0)\r\n" + "        (= s setEmptyT)) \r\n"
                + "        :pattern ((cardT s))\r\n" + "    ) \r\n" + ")))";
        SET_CARD_1.smt = "(assert (par (T)(= (cardT setEmptyT) 0)))";
        SET_CARD_2.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s (Set T))\r\n" + ")\r\n"
                + "    (! \r\n" + "        (>=  (cardT s) 0) \r\n" + "        :pattern ((cardT s))\r\n" + "    ) \r\n"
                + ")))";
        SET_CARD_3.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s1 (Set T))\r\n"
                + "    (s2 (Set T))\r\n" + ")\r\n" + "    (! \r\n" + "        (=> (subsetT s1 s2)\r\n"
                + "        (<= (cardT s1) (cardT s2))  \r\n" + "        ) \r\n" + "        :pattern ((cardT s))\r\n"
                + "    ) \r\n" + ")))";
        SET_CARD_4.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s (Set T))\r\n" + "    (t T)\r\n"
                + ")\r\n" + "    (! \r\n"
                + "        (= (cardT (store s t true))  (ite (select s t)  (cardT s) (+ (cardT s) 1) )) \r\n"
                + "        :pattern ((store s t true))\r\n" + "    ) \r\n" + ")))";

        // multisets
        MULTISET_1.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s1 (MultiSet T))\r\n"
                + "    (t T)\r\n" + ")\r\n" + "    (! \r\n" + "        (>= (msetselectT s1 t) 0)\r\n"
                + "         :pattern((msetselectT s1 t))\r\n" + "    ) \r\n" + ")))";
        MULTISET_2.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (t T)\r\n" + ")\r\n" + "    (! \r\n"
                + "        (= (msetselectT msetEmptyT t) 0)\r\n" + "         :pattern((msetselectT msetEmptyT t))\r\n"
                + "    ) \r\n" + ")))";
        MULTISET_3.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s1 (MultiSet T))\r\n"
                + "    (s2 (MultiSet T))\r\n" + "    (t T)\r\n" + ")\r\n" + "    (! \r\n"
                + "        (= (msetselectT (mintersectT s1 s2) t)\r\n"
                + "        (min (msetselectT s1 t) (msetselectT s2 t))\r\n"
                + "        ) :pattern((msetselectT s1 t) (msetselectT s2 t))\r\n" + "    ) \r\n" + ")))";
        MULTISET_4.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s1 (MultiSet T))\r\n"
                + "    (s2 (MultiSet T))\r\n" + "    (t T)\r\n" + ")\r\n" + "    (! \r\n"
                + "        (= (msetselectT (munionT s1 s2) t)\r\n"
                + "        (+ (msetselectT s1 t) (msetselectT s2 t))) \r\n"
                + "        :pattern((msetselectT s1 t) (msetselectT s2 t))\r\n" + "    ) \r\n" + ")))";
        MULTISET_5.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s1 (MultiSet T))\r\n"
                + "    (s2 (MultiSet T))\r\n" + "    (t T)\r\n" + ")\r\n" + "    (! \r\n"
                + "        (= (msetselectT (msetminusT s1 s2) t)\r\n"
                + "            (max (- (msetselectT s1 t)  (msetselectT s2 t))  0)\r\n" + "        )\r\n"
                + "        :pattern ((msetselectT s1 t) (msetselectT s2 t))\r\n" + "    ) \r\n" + ")))";
        MULTISET_6.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s1 (MultiSet T))\r\n"
                + "    (s2 (MultiSet T))\r\n" + "    (t T)\r\n" + ")\r\n" + "    (!\r\n"
                + "        (= (msubsetT s1 s2)\r\n" + "        (<=  (msetselectT s1 t) (msetselectT s2 t))\r\n"
                + "        ):pattern ((msetselectT s1 t) (msetselectT s2 t))\r\n" + "    )\r\n" + ")))";
        MULTISET_7.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s (MultiSet T))\r\n" + "    (t T)\r\n"
                + ")\r\n" + "    (!\r\n"
                + "        (= (msetselectT (msetinsertT s t) t) (+ (msetselectT s t) 1)) :pattern((msetinsertT s t))\r\n"
                + "    )\r\n" + "     \r\n" + ")))";
        MULTISET_8.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s (MultiSet T))\r\n" + ")\r\n"
                + "    (! \r\n" + "        (=> (= (mcardT s) 0)\r\n" + "        (= s msetEmptyT)) \r\n"
                + "        :pattern ((mcardT s))\r\n" + "    ) \r\n" + ")))";
        MULTISET_CARD_1.smt = "(assert (par (T) (= (mcardT msetEmptyT) 0)))";
        MULTISET_CARD_2.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s (MultiSet T))\r\n" + ")\r\n"
                + "    (! \r\n" + "        (>=  (mcardT s) 0) \r\n" + "        :pattern ((mcardT s))\r\n" + "    ) \r\n"
                + ")))";
        MULTISET_CARD_3.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s1 (MultiSet T))\r\n"
                + "    (s2 (MultiSet T))\r\n" + ")\r\n" + "    (! \r\n" + "        (=> (msubsetT s1 s2)\r\n"
                + "        (<= (mcardT s1) (mcardT s2))) \r\n" + "        :pattern ((msubsetT s1 s2))\r\n"
                + "    ) \r\n" + ")))";
        MULTISET_CARD_4.smt = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s (MultiSet T))\r\n"
                + "    (t T)\r\n" + ")\r\n" + "    (! \r\n"
                + "        (= (mcardT (msetinsertT s t))  (+ (mcardT s) 1))\r\n"
                + "        :pattern ((msetinsertT s t))\r\n" + "    ) \r\n" + ")))";

        // sequences
        SEQ_1.smt = "(assert (par (T) (\r\n" + "(forall\r\n" + "(\r\n" + "    (s (Seqq T))\r\n" + "    (t T)\r\n"
                + "    (i Int)\r\n" + ")\r\n" + "    (!\r\n" + "    (=> (and  (>= i 0) (<= i (seqlenT s))  )\r\n"
                + "    (= (seqgetT (seqappendT s t) i) (ite (= i (- (seqlenT s) 1) )  t  (seqgetT s i) )\r\n"
                + "    )):pattern ((seqappendT s t) (seqgetT s i))\r\n" + "      )\r\n" + "))))";
        SEQ_2.smt = "(assert (par (T) (\r\n" + "(forall\r\n" + "(\r\n" + "    (s1 (Seqq T))\r\n"
                + "    (s2 (Seqq T))\r\n" + "    (i Int)\r\n" + ")\r\n" + "    (!\r\n"
                + "    (=>  (and (>= i 0) (<= i (- (+ (seqlenT s1) (seqlenT s2)) 2)  ) )\r\n"
                + "    (= (seqgetT (seqconcatT s1 s2) i)   (ite (< (seqlenT s1) i)  (seqgetT s1 i) (seqgetT s2 i) )\r\n"
                + "      )):pattern ((seqconcatT s1 s2) (seqgetT s1 i))\r\n" + "      )\r\n" + "))))";
        SEQ_3.smt = "(assert (par (T) (\r\n" + "(forall\r\n" + "(\r\n" + "    (s (Seqq T))\r\n" + "    (i Int)\r\n"
                + "    (j Int)\r\n" + "    (k Int)\r\n" + ")\r\n" + "    (! \r\n"
                + "    (=> (and (<= 0 i k j) (< j (seqlenT s)) )\r\n"
                + "    (= (seqgetT (subseqselectT s i j) k)   (seqgetT s (+ i k)) \r\n"
                + "      )):pattern ((subseqselectT s i j) (seqgetT s k))\r\n" + "      )\r\n" + "))))";
        SEQ_4.smt = "(assert (par (T) (\r\n" + "(forall\r\n" + "(\r\n" + "    (s1 (Seqq T))\r\n"
                + "    (s2 (Seqq T))\r\n" + ")\r\n" + "    (! \r\n" + "    (=>\r\n"
                + "    (and (= (seqlenT s1) (seqlenT s2))\r\n" + "    (forall\r\n" + "    ((i Int))\r\n"
                + "    (!   \r\n" + "    (=> (and (>= 0 i) (< i (seqlenT s1)))\r\n"
                + "    (= (seqgetT s1 i)(seqgetT s2 i))) :pattern((seqgetT s1 i) (seqgetT s2 i))\r\n" + "    )))\r\n"
                + "    (= s1 s2)\r\n" + "    ) :pattern((seqlenT s1) (seqlenT s2))\r\n" + ")))))";
        SEQ_5.smt = "(assert (par (T) (\r\n" + "(forall\r\n" + "(\r\n" + "    (s (Seqq T))\r\n" + ")\r\n"
                + "    (! \r\n" + "    (=>  (= (seqlenT s) 0) \r\n" + "    (= s emtpyseqT)\r\n"
                + "    ):pattern ((seqlenT s))\r\n" + "    )\r\n" + "))))";
        SEQ_LEN_1.smt = "(assert (par (T) ((= (seqlenT emtpyseqT) 0))))";
        SEQ_LEN_2.smt = "(assert (par (T) (\r\n" + "(forall\r\n" + "(\r\n" + "    (s (Seqq T))\r\n" + ")\r\n"
                + "    (! \r\n" + "    (>= (seqlenT s) 0):pattern((seqlenT s))\r\n" + "    ) \r\n" + "))))";
        SEQ_LEN_3.smt = "(assert (par (T) (\r\n" + "(forall\r\n" + "(\r\n" + "    (s (Seqq T))\r\n" + "    (t T)\r\n"
                + ")\r\n" + "    (! \r\n"
                + "    (= (seqlenT (seqappendT s t)) (+ (seqlenT s) 1)) :pattern((seqappendT s t))\r\n" + "    ) \r\n"
                + "))))";
        SEQ_LEN_4.smt = "(assert (par (T) (\r\n" + "(forall\r\n" + "(\r\n" + "    (s (Seqq T))\r\n" + "    (i Int)\r\n"
                + "    (j Int)\r\n" + ")\r\n" + "    (!\r\n" + "    (=>  (<= i j)\r\n"
                + "    (= (seqlenT (subseqselectT s i j)) (+ (- j i) 1))) :pattern((subseqselectT s i j))\r\n"
                + "    )\r\n" + "))))";
        SEQ_LEN_5.smt = "(assert (par (T) (\r\n" + "(forall\r\n" + "(\r\n" + "    (s1 (Seqq T))\r\n"
                + "    (s2 (Seqq T))\r\n" + ")\r\n" + "    (! \r\n"
                + "    (= (seqlenT (seqconcatT s1 s2)) (+ (seqlenT s1) (seqlenT s2))) :pattern((seqconcatT s1 s2))\r\n"
                + "    ) \r\n" + "))))";

        // Heap/Arrays
        ARR_1.smt = "(assert (par (T) (\r\n" + "(forall\r\n" + "(\r\n" + "    (i Int)\r\n" + "    (h Heap)\r\n"
                + "    (a (Arr T))\r\n" + "    (v T)\r\n" + ")\r\n" + "(!\r\n"
                + "    (= (arrselectT (arrstoreT h a i v) a i) v) :pattern((arrstoreT h a i v))\r\n" + ")))))";
        ARR2_1.smt = "(assert (par (T) (\r\n" + "(forall\r\n" + "(\r\n" + "    (i Int)\r\n" + "    (j Int)\r\n"
                + "    (h Heap)\r\n" + "    (a (Arr2 T))\r\n" + "    (v T)\r\n" + ")\r\n" + "(!\r\n"
                + "    (= (arr2selectT (arr2storeT h a i j v) a i j) v) :pattern((arr2storeT h a i j v) )\r\n"
                + ")))))";
        HEAP_1.smt = "(assert (par (C T) (\r\n" + "(forall\r\n" + "(\r\n" + "    (v T)\r\n" + "    (h Heap)\r\n"
                + "    (c C)\r\n" + "    (f (Field C T))\r\n" + "\r\n" + ")\r\n" + "(!\r\n" + "  \r\n"
                + "    (= (fieldselectC.T (fieldstoreC.T h c f v) c f) v) :pattern((fieldstoreC.T h c f v))\r\n"
                + ")))))";
        HEAP_2.smt = "(assert (par (C T) (\r\n" + "(forall\r\n" + "(\r\n" + "    (v T)\r\n" + "    (h Heap)\r\n"
                + "    (c1 C)\r\n" + "    (c2 C)\r\n" + "    (f1 (Field C T))\r\n" + "    (f2 (Field C T))\r\n" + "\r\n"
                + ")\r\n" + "(!\r\n" + "    (=> (or (distinct c1 c2) (distinct f1 f2))\r\n"
                + "    (= (fieldselectC.T (fieldstoreC.T h c1 f1 v) c2 f2) (fieldselectC.T h c2 f2)))\r\n"
                + "     :pattern((fieldstoreC.T h c1 f1 v) (fieldstoreC.T h c2 f2 v))\r\n" + ")))))";
        HEAP_3.smt = "(assert (forall\r\n" + "(\r\n" + "    (h Heap)\r\n" + "    (o Object)\r\n" + "\r\n" + ")\r\n"
                + "(!\r\n" + "    (= (created (create h o) o ) true) :pattern((create h o))\r\n" + ")))";
        HEAP_4.smt = "(assert (par (C T) (\r\n" + "(forall\r\n" + "(\r\n" + "    (c C)\r\n" + "    (h1 Heap)\r\n"
                + "    (h2 Heap)\r\n" + "    (s (Set Object))\r\n" + "    (f (Field C T))\r\n" + ")\r\n" + "(! \r\n"
                + "    (= (fieldselectC.T (anon h1 s h2) c f) (fieldselectC.T (ite (select s (c2o c)) h2 h1) c f)) :pattern((anon h1 s h2) (fieldselectC.T h1 c f))    \r\n"
                + ")))))";
        HEAP_5.smt = "(assert (par (C) ((forall ((c C)) (! (= (o2c (c2o c)) c) :pattern ((o2c (c2o c))))))))\r\n";
        HEAP_6.smt = "(assert (par (C) ((forall ((o Object)) (=> (= (typeOf o) Type.C) (= (c2o (o2c o)) o))))))";

    }

    private String smt;

    public String getSmt() {
        return smt;
    }

}
