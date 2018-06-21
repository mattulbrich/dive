package edu.kit.iti.smttrans.access;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import edu.kit.iti.algover.smttrans.access.Response;
import edu.kit.iti.algover.smttrans.access.SolverResponse;
import edu.kit.iti.algover.smttrans.access.Z3Access;

public class Z3AccessTest {
    @Test
    public void unsatTest() throws Exception {
        
        String smt = "\r\n" + "            (declare-sort Heap 0)\r\n" + "      (declare-sort ArrInt 0)\r\n"
                + "      (declare-const ~a ArrInt)\r\n" + "      (declare-const ~null ArrInt)\r\n"
                + "      (declare-const ~heap Heap)\r\n" + "      (declare-const ~i Int)\r\n"
                + "      (declare-const ~max Int)\r\n" + "      (declare-const ~k Int)\r\n"
                + "      (declare-fun arrselectInt (Heap (ArrInt) Int) Int)\r\n"
                + "      (declare-fun arrstoreInt (Heap (ArrInt) Int Int) Heap)\r\n"
                + "      (declare-fun arrlenInt (ArrInt) Int)\r\n" + "      (assert (forall\r\n" + "      (\r\n"
                + "          (i Int)\r\n" + "          (h Heap)\r\n" + "          (a (ArrInt))\r\n"
                + "          (v Int)\r\n" + "      )\r\n" + "      (!\r\n"
                + "          (= (arrselectInt (arrstoreInt h a i v) a i) v) :pattern((arrstoreInt h a i v))\r\n"
                + "      )))\r\n" + "      (assert (forall\r\n" + "      (\r\n" + "          (a (ArrInt))\r\n"
                + "      )\r\n" + "      (!\r\n" + "          (> (arrlenInt a) 0) :pattern((arrlenInt a))\r\n"
                + "      )))\r\n" + "     \r\n" + "      (assert (not (= ~a ~null)))\r\n"
                + "      (assert (>= (arrlenInt ~a) 1))\r\n" + "      (assert (= ~max (arrselectInt ~heap ~a 0)))\r\n"
                + "      (assert(= ~i 1))\r\n"
                + "      (assert(not (forall((k Int))(=> (and (<= 0 ~k) (< ~k ~i)) (<= (arrselectInt ~heap ~a ~k) ~max)))))";
        Z3Access a = new Z3Access();
        SolverResponse r = a.accessSolver(smt);
        assertEquals(r.getResponse(), Response.UNSAT);

    }

    @Test
    public void modelTest() throws Exception {
        String smt = "      (declare-sort SetInt 0)\r\n" + "      (declare-const ~s2 SetInt)\r\n"
                + "      (declare-const setEmptyInt (SetInt))\r\n" + "      (declare-const ~s1 SetInt)\r\n"
                + "      (declare-fun unionInt (SetInt SetInt) (SetInt))\r\n"
                + "      (declare-fun inSetInt ((SetInt) Int)  Bool)\r\n"
                + "      (declare-fun setInsertInt ((SetInt) Int) (SetInt))\r\n"
                + "      (declare-fun setcardInt (SetInt) Int)\r\n" + "      (assert (forall\r\n" + "      (\r\n"
                + "          (s1 SetInt)\r\n" + "          (s2 SetInt)\r\n" + "          (t Int)\r\n" + "      )\r\n"
                + "          (!\r\n" + "              (= (inSetInt (unionInt s1 s2) t)\r\n"
                + "              (or (inSetInt s1 t) (inSetInt s2 t)))\r\n"
                + "              :pattern (( inSetInt (unionInt s1 s2) t))\r\n" + "          )\r\n" + "      ))\r\n"
                + "      (assert (forall\r\n" + "      (\r\n" + "          (s1 SetInt)\r\n" + "          (t Int)\r\n"
                + "      )\r\n" + "          (!\r\n" + "              (= (inSetInt (setInsertInt s1 t) t) true)\r\n"
                + "              :pattern ((inSetInt (setInsertInt s1 t) t))\r\n" + "          )\r\n" + "      ))\r\n"
                + "      (assert (forall\r\n" + "      (\r\n" + "          (s SetInt)\r\n" + "      )\r\n"
                + "          (!\r\n" + "              (=> (= (setcardInt s) 0)\r\n"
                + "              (= s setEmptyInt))\r\n" + "              :pattern ((setcardInt s))\r\n"
                + "          )\r\n" + "      ))\r\n" + "      (assert (= (setcardInt setEmptyInt) 0))\r\n"
                + "      (assert (forall\r\n" + "      (\r\n" + "          (s (SetInt))\r\n" + "      )\r\n"
                + "          (!\r\n" + "              (>=  (setcardInt s) 0)\r\n"
                + "              :pattern ((setcardInt s))\r\n" + "          )\r\n" + "      ))\r\n" + "     \r\n"
                + "      (assert (< (setcardInt ~s1) 3))\r\n" + "      (assert (> (setcardInt ~s2) 5))\r\n"
                + "      (assert (not(> (setcardInt (unionInt ~s1 ~s2)) 4)))";
        Z3Access a = new Z3Access();
        SolverResponse r = a.accessSolver(smt);
        assertEquals(r.getResponse(), Response.SAT);
        // r.getModel()

    }
}
