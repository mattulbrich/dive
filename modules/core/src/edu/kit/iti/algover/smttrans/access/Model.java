package edu.kit.iti.algover.smttrans.access;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Model {

    // private static Pattern defFun = Pattern.compile("\\(define-fun(.*?)\\)");

    private Map<String, List<String>> aMap;
    private List<String> contents;
    private static final String DECL = "(declare-fun";
    private static final String DEF = "(define-fun";

    public Model(List<String> contents) {
        this.contents = contents;
        this.aMap = parseModel();
     //   System.out.println(aMap.toString());

    }

    /**
     * z3 (define-fun c () Int 1) [java] [java] [java] (define-fun b () Int 1)
     * [java] [java] [java] (define-fun a () Int 1) [java] [java] [java] (define-fun
     * d () Int (- 3))
     * 
     * @return
     */

    /**
     * cvc4
     * 
     * [java] (model [java] (define-fun a () Int 1) [java] (define-fun b () Int 1)
     * [java] (define-fun c () Int 1) [java] (define-fun d () Int (- 3)) [java] )
     * 
     * @return
     */

    /**
     * (model [java] ;; universe for SetInt: [java] ;; SetInt!val!2 SetInt!val!4
     * SetInt!val!1 SetInt!val!0 SetInt!va l!3 [java] ;; ----------- [java] ;;
     * definitions for universe elements: [java] (declare-fun SetInt!val!2 ()
     * SetInt) [java] (declare-fun SetInt!val!4 () SetInt) [java] (declare-fun
     * SetInt!val!1 () SetInt) [java] (declare-fun SetInt!val!0 () SetInt) [java]
     * (declare-fun SetInt!val!3 () SetInt) [java] ;; cardinality constraint: [java]
     * (forall ((x SetInt)) [java] (or (= x SetInt!val!2) [java] (= x SetInt!val!4)
     * [java] (= x SetInt!val!1) [java] (= x SetInt!val!0) [java] (= x
     * SetInt!val!3))) [java] ;; ----------- [java] (define-fun setEmptyInt ()
     * SetInt [java] SetInt!val!0) [java] (define-fun s2 () SetInt [java]
     * SetInt!val!2) [java] (define-fun s1 () SetInt [java] SetInt!val!1) [java]
     * (define-fun inSetInt ((x!0 SetInt) (x!1 Int)) Bool [java] true) [java]
     * (define-fun setInsertInt ((x!0 SetInt) (x!1 Int)) SetInt [java] SetInt!val!4)
     * [java] (define-fun setcardInt!16 ((x!0 SetInt)) Int [java] (ite (= x!0
     * SetInt!val!0) 0 [java] (ite (= x!0 SetInt!val!2) 6 [java] 1))) [java]
     * (define-fun k!15 ((x!0 SetInt)) SetInt [java] (ite (= x!0 SetInt!val!0)
     * SetInt!val!0 [java] (ite (= x!0 SetInt!val!2) SetInt!val!2 [java] (ite (= x!0
     * SetInt!val!4) SetInt!val!4 [java] (ite (= x!0 SetInt!val!1) SetInt!val!1
     * [java] SetInt!val!3))))) [java] (define-fun setcardInt ((x!0 SetInt)) Int
     * [java] (setcardInt!16 (k!15 x!0))) [java] (define-fun unionInt ((x!0 SetInt)
     * (x!1 SetInt)) SetInt [java] SetInt!val!3) [java] )
     * 
     * @return
     */
    /**
     * Decl: (declare-fun SetInt!val!2 () SetInt) [java] Decl: (declare-fun
     * SetInt!val!4 () SetInt) [java] Decl: (declare-fun SetInt!val!1 () SetInt)
     * [java] Decl: (declare-fun SetInt!val!0 () SetInt) [java] Decl: (declare-fun
     * SetInt!val!3 () SetInt)
     * 
     * 
     * @return
     */

    private static Map<String, String> m1 = new HashMap<>();
    private static Map<String, List<String>> m2 = new HashMap<>();
    
    
    
    //TODO
    private Map<String, List<String>> parseModel() {
        System.out.println();
        HashMap<String, List<String>> m = new HashMap<>();
        for (String d : contents) {
            String line = d.trim();
            System.out.println();
            System.out.println(line);
            System.out.println();
            if (line.startsWith(DEF) && line.contains("~")) {

                String[] parts = line.split("(?<![\\(,\\)])\\s+");

                String k = "";
                String v = "";
                for (String p : parts) {

                    if (p.contains("~")) {
                        k = p;
                        continue;
                    }
                    if (p.contains("val")) {
                        v = p;
                        continue;
                    }
                }
                m1.put(k, v.substring(0, v.length() - 1));
            }

        }

        for (String v : m1.values()) {

            List<String> s = new ArrayList<>();

            for (String d : contents) {
                String line = d.trim();
                if (line.startsWith(DEF) && line.contains(v) && !line.contains("~"))
                    s.add(line);

            }

            m2.put(v, s);
        }

        return mergeMaps(m1, m2);
    }

    private static <K1, K2, K3, K4> Map<K1, K4> mergeMaps(Map<K1, K2> m1, Map<K3, K4> m2) {
        Map<K1, K4> m3 = new HashMap<K1, K4>();
        for (K1 key : m1.keySet()) {
            m3.put(key, m2.get(m1.get(key)));
        }
        return m3;
    }

    @Override
    public String toString() {

        // for (String s : contents) {
        // System.out.println();
        // System.out.println(s);
        // System.out.println();
        // }
        return contents.toString();
    }

//    private String getAssignment(String name) {
//        return aMap.get(name);
//
//    }
}
