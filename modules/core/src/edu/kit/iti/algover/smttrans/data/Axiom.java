package edu.kit.iti.algover.smttrans.data;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import edu.kit.iti.algover.smttrans.translate.Names;

public enum Axiom {

    /**
     * Functions
     */

    // sets
    SETIN, SETADD, SETCARD, SETMINUS, SETUNION, SETINTERSECT, SETSUBSET,

    // multisets
    MSETADD, MSETUNION, MSETINTERSECT, MSETMINUS, MSETCARD, MSETQUANT, MSETIN, MSETSUBSET, MSETMIN, MSETMAX,
    // sequences
    SEQLEN, SEQGET, SEQUPD, SEQCONS, SEQSUBSELECT, SEQCONCAT,
    // Heap/Arrays
    ANON, EVERYTHING, CREATE, ISCREATED, ARRLEN, ARR2LEN0, ARR2LEN1, FIELDSELECT, FIELDSTORE, ARRSELECT, ARRSTORE, ARR2SELECT, ARR2STORE,

    /**
     * Axioms
     */

    // sets
    S1, S2, S3, S4, S5, S6, S7, SC1, SC2, SC3,

    // multisets
    MS1, MS2, MS3, MS4, MS5, MS6, MS7, MS8, MSC1, MSC2, MSC3,
    // sequences

    SQ1, SQ2, SQ3, SQ4, SQ5, SQ6, SQL1, SQL2, SQL3, SQL4, SQL5,

    // Heap/Arrays
    A11, A12, A13, A14, A1L1, A21, A22, A23, A24, A2L0, A2L1, H1, H2, H3, H4, H5, H6, H7, H8, H9;
    static {

        /**
         * Sorts
         */

        // sets
        // SET_INST.smt = "(define-sort Set (T) (Array T Bool))"; //TODO
        // SETEMPTY_INST.smt = "(declare-const (par (T) (setEmpty<T> (Set<T>))))";

        // Heap/Arrays

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
        MSETADD.smt = "(declare-fun (par (T) (msetadd<T> (T MultiSet<T>) MultiSet<T>)))";
        MSETUNION.smt = "(declare-fun (par (T) (msetunion<T> (MultiSet<T> MultiSet<T>) MultiSet<T>)))";
        MSETINTERSECT.smt = "(declare-fun (par (T) (msetintersect<T> (MultiSet<T> MultiSet<T>) MultiSet<T>)))";
        MSETMINUS.smt = "(declare-fun (par (T) (msetminus<T> (MultiSet<T> MultiSet<T>) MultiSet<T>)))";
        MSETCARD.smt = "(declare-fun (par (T) (msetcard<T> (MultiSet<T>) Int)))";
        MSETQUANT.smt = "(declare-fun (par (T) (mquant<T> (T MultiSet<T>) Int)))";
        MSETIN.smt = "(declare-fun (par (T) (msetin<T> (T MultiSet<T>) Bool)))";
        MSETSUBSET.smt = "(declare-fun (par (T) (msetsubset<T> (MultiSet<T> MultiSet<T>) Bool)))";
        MSETMIN.smt = "(define-fun min ((x Int) (y Int)) Int\r\n" + "  (ite (<= x y) x y))";
        MSETMAX.smt = "(define-fun max ((x Int) (y Int)) Int\r\n" + "  (ite (<= x y) y x))";

        // sequences
        SEQLEN.smt = "(declare-fun (par (T) (seqlen<T> (Seq<T>) Int)))";
        SEQGET.smt = "(declare-fun (par (T) (seqget<T> (Seq<T> Int) T)))";
        SEQUPD.smt = "(declare-fun (par (T) (sequpd<T> (Seq<T> T Int) Seq<T>)))";
        SEQCONS.smt = "(declare-fun (par (T) (seqcons<T> (T Seq<T>) Seq<T>)))";
        SEQSUBSELECT.smt = "(declare-fun (par (T) (seqsubselect<T> (Seq<T> Int Int) Seq<T>)))";
        SEQCONCAT.smt = "(declare-fun (par (T) (seqconcat<T> (Seq<T> Seq<T>) Seq<T>)))";

        // Heap/Arrays

        ANON.smt = "(declare-fun anon (Heap Set<Object> Heap) Heap)";
        EVERYTHING.smt = "(assert (forall ((o Object)) (setin<Object> o " + Names.getPrefix() + "everything)))";
        EVERYTHING.dependencies = new HashSet<>(Arrays.asList(Axiom.SETIN, Axiom.SETADD)); // SETADD ?
        CREATE.smt = "(declare-fun create (Heap Object) Heap)";
        ISCREATED.smt = "(declare-fun isCreated (Heap Object) Bool)";
        ARRLEN.smt = "(declare-fun (par (T) (arrlen<T> (Arr<T>) Int)))";
        ARR2LEN0.smt = "(declare-fun (par (T) (arr2len0<T> (Arr2<T>) Int)))";
        ARR2LEN1.smt = "(declare-fun (par (T) (arr2len1<T> (Arr2<T>) Int)))";
        FIELDSELECT.smt = "(declare-fun (par (C T) (fieldselect<C.T> (Heap C Field<C.T>) T)))";
        FIELDSTORE.smt = "(declare-fun (par (C T) (fieldstore<C.T> (Heap C Field<C.T> T) Heap)))";
        ARRSELECT.smt = "(declare-fun (par (T) (arrselect<T> (Heap Arr<T> Int) T)))";
        ARRSTORE.smt = "(declare-fun (par (T) (arrstore<T> (Heap Arr<T> Int T) Heap)))";
        ARR2STORE.smt = "(declare-fun (par (T) (arr2store<T> (Heap Arr2<T> Int Int T) Heap)))";
        ARR2SELECT.smt = "(declare-fun (par (T) (arr2select<T> (Heap Arr2<T> Int Int) T)))";

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
        MS1.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (s MultiSet<T>)\r\n" + "    (t T)\r\n" + ")\r\n"
                + "(= (msetin<T> t s) (> (mquant<T> t s) 0)))))";
        MS1.dependencies = new HashSet<>(Arrays.asList(Axiom.MS4,Axiom.MSETIN, Axiom.MSETQUANT));
        MS2.smt = "(assert (par (T) (forall \r\n" + "(\r\n" + "    (x T)\r\n" + ")\r\n"
                + "(= (mquant<T> x ~msetempty<T>) 0))))";
        MS2.dependencies = new HashSet<>(Arrays.asList(Axiom.MS4,Axiom.MSETQUANT));
        MS3.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (s MultiSet<T>)\r\n" + "    (x T)\r\n"
                + "    (y T)\r\n" + ")\r\n" + "(! \r\n"
                + "(= (mquant<T> y (msetadd<T> x s)) (ite (= x y) (+ (mquant<T> x s) 1) (mquant<T> y s)))\r\n"
                + ":pattern((mquant<T> y s) (msetadd<T> x s))))))";
        MS3.dependencies = new HashSet<>(Arrays.asList(Axiom.MS4,Axiom.MSETADD, Axiom.MSETQUANT));
        MS4.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "(s1 MultiSet<T>)\r\n" + "(s2 MultiSet<T>)\r\n" + ")\r\n"
                + "(=>  \r\n" + "(forall \r\n" + "(\r\n" + "    (t T)\r\n" + ")\r\n"
                + "(= (mquant<T> t s1) (mquant<T> t s2))) (= s1 s2)))))";
        MS4.dependencies = new HashSet<>(Arrays.asList(Axiom.MSETQUANT));
        MS5.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (s1 MultiSet<T>)\r\n" + "    (s2 MultiSet<T>)\r\n"
                + "    (x T)\r\n" + ")\r\n" + "(! \r\n"
                + "(= (mquant<T> x (msetunion<T> s1 s2)) (+ (mquant<T> x s1) (mquant<T> x s2)))\r\n"
                + ":pattern((msetunion<T> s1 s2) (mquant<T> x s1))))))";
        MS5.dependencies = new HashSet<>(Arrays.asList(Axiom.MS4,Axiom.MSETUNION, Axiom.MSETQUANT));
        MS6.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (s1 MultiSet<T>)\r\n" + "    (s2 MultiSet<T>)\r\n"
                + "    (x T)\r\n" + ")\r\n" + "(! \r\n"
                + "(= (mquant<T> x (msetintersect<T> s1 s2)) (min (mquant<T> x s1) (mquant<T> x s2)))\r\n"
                + ":pattern((msetintersect<T> s1 s2) (mquant<T> x s1))))))";
        MS6.dependencies = new HashSet<>(Arrays.asList(Axiom.MS4,Axiom.MSETINTERSECT, Axiom.MSETQUANT, Axiom.MSETMIN));
        MS7.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (s1 MultiSet<T>)\r\n" + "    (s2 MultiSet<T>)\r\n"
                + "    (x T)\r\n" + ")\r\n" + "(!\r\n"
                + "(= (mquant<T> x (msetminus<T> s1 s2)) (max (- (mquant<T> x s1) (mquant<T> x s2)) 0 ))\r\n"
                + ":pattern((msetminus<T> s1 s2) (mquant<T> x s1))))))";
        MS7.dependencies = new HashSet<>(Arrays.asList(Axiom.MSETMAX,Axiom.MS4,Axiom.MSETMINUS, Axiom.MSETQUANT, Axiom.MSETMAX));

        MS8.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "(s1 MultiSet<T>)\r\n" + "(s2 MultiSet<T>)\r\n" + ")\r\n"
                + "(= (msetsubset<T> s1 s2) \r\n" + "(forall \r\n" + "(\r\n" + "    (t T)\r\n" + ")\r\n" + "(!\r\n"
                + "(<= (mquant<T> t s1) (mquant<T> t s2)) \r\n"
                + ":pattern((msetsubset<T> s1 s2) (mquant<T> t s1) (mquant<T> t s2))))))))";
        MS8.dependencies = new HashSet<>(Arrays.asList(Axiom.MS4,Axiom.MSETSUBSET, Axiom.MSETQUANT));

        MSC1.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (s MultiSet<T>)\r\n" + ")\r\n" + "(!\r\n"
                + "(>= (msetcard<T> s) 0) \r\n" + ":pattern((msetcard<T> s))))))";
        MSC1.dependencies = new HashSet<>(Arrays.asList(Axiom.MSETCARD));

        MSC2.smt = "(assert (par (T) (= (msetcard<T> ~msetempty<T>) 0)))";
        MSC2.dependencies = new HashSet<>(Arrays.asList(Axiom.MSETCARD));
        MSC3.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (s MultiSet<T>)\r\n" + "    (t T)\r\n" + ")\r\n"
                + "(!\r\n" + "(= (msetcard<T> (msetadd<T> t s)) (+ (msetcard<T> s) 1))\r\n"
                + ":pattern((msetadd<T> t s))))))";
        MSC3.dependencies = new HashSet<>(Arrays.asList(Axiom.MSETCARD, Axiom.MSETADD));
        // sequences
        SQ1.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (i Int)\r\n" + "    (j Int)\r\n"
                + "    (s Seq<T>)\r\n" + "    (t T)\r\n" + ")\r\n"
                + "(= (seqget<T> (sequpd<T> s t i) j) (ite (= i j) t (seqget<T> s j))))))";
        SQ1.dependencies = new HashSet<>(Arrays.asList(Axiom.SEQGET, Axiom.SEQUPD));
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

        A11.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (h Heap)\r\n" + "    (a Arr<T>)\r\n"
                + "    (i Int)\r\n" + "    (j Int)\r\n" + "    (v T)\r\n" + ")\r\n"
                + "(= (arrselect<T> (arrstore<T> h a i v) a j) (ite (= i j) v (arrselect<T> h a j))))))";
        A11.dependencies = new HashSet<>(Arrays.asList(Axiom.ARRSELECT, Axiom.ARRSTORE));
        A12.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (h Heap)\r\n" + "    (a Arr<T>)\r\n"
                + "    (i Int)\r\n" + "    (o Object)\r\n" + ")\r\n"
                + "(= (arrselect<T> (create h o) a i) (arrselect<T> h a i)))))";
        A12.dependencies = new HashSet<>(Arrays.asList(Axiom.ARRSELECT, Axiom.CREATE));
        A13.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (h Heap)\r\n" + "    (a1 Arr<T>)\r\n"
                + "    (a2 Arr2<T>)\r\n" + "    (i Int)\r\n" + "    (j Int)\r\n" + "    (k Int)\r\n"
                + "    (o Object)\r\n" + "    (v T)\r\n" + ")\r\n"
                + "(= (arrselect<T> (arr2store<T> h a2 i j v) a1 k) (arrselect<T> h a1 k)))))";
        A13.dependencies = new HashSet<>(Arrays.asList(Axiom.ARRSELECT, Axiom.ARR2STORE));
        A14.smt = "(assert (par (C T) (forall\r\n" + "(\r\n" + "    (h Heap)\r\n" + "    (a Arr<T>)\r\n"
                + "    (f Field<C.T>)\r\n" + "    (i Int)\r\n" + "    (o C)\r\n" + "    (v T)\r\n" + ")\r\n"
                + "(= (arrselect<T> (fieldstore<C.T> h o f v) a i) (arrselect<T> h a i)))))";
        A14.dependencies = new HashSet<>(Arrays.asList(Axiom.ARRSELECT, Axiom.FIELDSTORE));
        A1L1.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (a Arr<T>)\r\n" + ")\r\n"
                + "(>= (arrlen<T> a) 0))))";
        A1L1.dependencies = new HashSet<>(Arrays.asList(Axiom.ARRLEN));
        A21.smt = "(assert (par (T) (forall \r\n" + "(\r\n" + "    (h Heap)\r\n" + "    (a Arr2<T>)\r\n"
                + "    (i Int)\r\n" + "    (j Int)\r\n" + "    (l Int)\r\n" + "    (k Int)\r\n" + "    (v T)\r\n"
                + ")\r\n"
                + "(= (arr2select<T> (arr2store<T> h a i j v) a l k) (ite (and (= i l) (= j k)) v (arr2select<T> h a j l))))))";
        A21.dependencies = new HashSet<>(Arrays.asList(Axiom.ARR2SELECT, ARR2STORE));
        A22.smt = "(assert (par (T) (forall \r\n" + "(\r\n" + "    (h Heap)\r\n" + "    (a Arr2<T>)\r\n"
                + "    (o Object)\r\n" + "    (i Int)\r\n" + "    (j Int)\r\n" + ")\r\n"
                + "(= (arr2select<T> (create h o) a i j)  (arr2select<T> h a i j)))))";
        A22.dependencies = new HashSet<>(Arrays.asList(Axiom.ARR2SELECT, CREATE));
        A23.smt = "(assert (par (T) (forall \r\n" + "(\r\n" + "    (h Heap)\r\n" + "    (a1 Arr<T>)\r\n"
                + "    (a2 Arr2<T>)\r\n" + "    (o Object)\r\n" + "    (i Int)\r\n" + "    (j Int)\r\n"
                + "    (k Int)\r\n" + "    (v T)\r\n" + ")\r\n"
                + "(= (arr2select<T> (arrstore<T> h a1 k v) a2 i j)  (arr2select<T> h a2 i j)))))";
        A23.dependencies = new HashSet<>(Arrays.asList(Axiom.ARR2SELECT, Axiom.ARRSTORE));
        A24.smt = "(assert (par (C T) (forall \r\n" + "(\r\n" + "    (h Heap)\r\n" + "    (a Arr2<T>)\r\n"
                + "    (o C)\r\n" + "    (f Field<C.T>)\r\n" + "    (d T)\r\n" + "    (i Int)\r\n" + "    (j Int)\r\n"
                + ")\r\n" + "(= (arr2select<T> (fieldstore<C.T> h o f d) a i j)  (arr2select<T> h a i j)))))";
        A24.dependencies = new HashSet<>(Arrays.asList(Axiom.ARR2SELECT, FIELDSTORE));
        A2L0.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (a Arr2<T>)\r\n" + ")\r\n"
                + "(>= (arr2len0<T> a) 0))))";
        A2L0.dependencies = new HashSet<>(Arrays.asList(Axiom.ARR2LEN0));
        A2L1.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (a Arr2<T>)\r\n" + ")\r\n"
                + "(>= (arr2len1<T> a) 0))))";
        A2L1.dependencies = new HashSet<>(Arrays.asList(Axiom.ARR2LEN1));
        H1.smt = "(assert (par (C T) (forall\r\n" + "(\r\n" + "    (o1 C)\r\n" + "    (o2 C)\r\n"
                + "    (f1 Field<C.T>)\r\n" + "    (f2 Field<C.T>)\r\n" + "    (h Heap)\r\n" + "    (v T)\r\n" + ")\r\n"
                + "(= (fieldselect<C.T> (fieldstore<C.T> h o1 f1 v) o2 f2) (ite (and (= o1 o2) (= f1 f2)) v (fieldselect<C.T> h o2 f2))))))";
        H1.dependencies = new HashSet<>(Arrays.asList(Axiom.FIELDSELECT, Axiom.FIELDSTORE));

        H2.smt = "(assert (par (C T) (forall\r\n" + "(\r\n" + "    (o C)\r\n" + "    (a Arr<T>)\r\n"
                + "    (f Field<C.T>)\r\n" + "    (h Heap)\r\n" + "    (v T)\r\n" + "    (i Int)\r\n" + ")\r\n"
                + "(= (fieldselect<C.T> (arrstore<T> h a i v) o f) (fieldselect<C.T> h o f)))))";
        H2.dependencies = new HashSet<>(Arrays.asList(Axiom.FIELDSELECT, Axiom.ARRSTORE));

        H3.smt = "(assert (par (C T) (forall\r\n" + "(\r\n" + "    (o C)\r\n" + "    (a Arr2<T>)\r\n"
                + "    (f Field<C.T>)\r\n" + "    (h Heap)\r\n" + "    (v T)\r\n" + "    (i Int)\r\n"
                + "    (j Int)\r\n" + ")\r\n"
                + "(= (fieldselect<C.T> (arr2store<T> h a i j v) o f) (fieldselect<C.T> h o f)))))";
        H3.dependencies = new HashSet<>(Arrays.asList(Axiom.FIELDSELECT, Axiom.ARR2STORE));
        H4.smt = "(assert (par (C T) (forall\r\n" + "(\r\n" + "    (o1 C)\r\n" + "    (o2 Object)\r\n"
                + "    (a Arr<T>)\r\n" + "    (f Field<C.T>)\r\n" + "    (h Heap)\r\n" + "    (v T)\r\n"
                + "    (i Int)\r\n" + ")\r\n"
                + "(= (fieldselect<C.T> (create h o2) o1 f) (fieldselect<C.T> h o1 f)))))";
        H4.dependencies = new HashSet<>(Arrays.asList(Axiom.FIELDSELECT, Axiom.CREATE));
        H5.smt = "(assert (forall\r\n" + "(\r\n" + "    (o Object)\r\n" + "    (h Heap)\r\n" + ")\r\n"
                + "(isCreated (create h o) o)))";
        H5.dependencies = new HashSet<>(Arrays.asList(Axiom.ISCREATED, Axiom.CREATE));
        H6.smt = "(assert (par (C T) (forall\r\n" + "(\r\n" + "    (h Heap)\r\n" + "    (c C)\r\n"
                + "    (f Field<C.T>)\r\n" + "    (v T)\r\n" + "    (o Object)\r\n" + ")\r\n"
                + "(= (isCreated (fieldstore<C.T> h c f v) o) (isCreated h o)))))";
        H6.dependencies = new HashSet<>(Arrays.asList(Axiom.ISCREATED, Axiom.FIELDSTORE));
        H7.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (h Heap)\r\n" + "    (v T)\r\n" + "    (o Object)\r\n"
                + "    (i Int)\r\n" + "    (a Arr<T>)\r\n" + ")\r\n"
                + "(= (isCreated (arrstore<T> h a i v) o) (isCreated h o)))))";
        H7.dependencies = new HashSet<>(Arrays.asList(Axiom.ISCREATED, Axiom.ARRSTORE));
        H8.smt = "(assert (par (T) (forall\r\n" + "(\r\n" + "    (h Heap)\r\n" + "    (v T)\r\n" + "    (o Object)\r\n"
                + "    (i Int)\r\n" + "    (j Int)\r\n" + "    (a Arr2<T>)\r\n" + ")\r\n"
                + "(= (isCreated (arr2store<T> h a i j v) o) (isCreated h o)))))";
        H8.dependencies = new HashSet<>(Arrays.asList(Axiom.ISCREATED, Axiom.ARR2STORE));

        H9.smt = "(assert (par (C T) (forall\r\n" + "(\r\n" + "    (c C)\r\n" + "    (h1 Heap)\r\n"
                + "    (h2 Heap)\r\n" + "    (s Set<Object>)\r\n" + "    (f Field<C.T>)\r\n" + ")\r\n"
                + "(= (fieldselect<C.T> (anon h1 s h2) c f) (fieldselect<C.T> (ite (setin<Object> s (c2o c)) h2 h1) c f)))))";
        H9.dependencies = new HashSet<>(Arrays.asList(Axiom.SETIN, Axiom.FIELDSELECT, Axiom.ANON));
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