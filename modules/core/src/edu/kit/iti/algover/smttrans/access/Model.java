package edu.kit.iti.algover.smttrans.access;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Model {
    
//    private static Pattern defFun = Pattern.compile("\\(define-fun(.*?)\\)");

    private Map<String,String> aMap;
    private List<String> contents;
    private static final String DECL = "(declare-fun";
    private static final String DEF = "(define-fun";
    
    public Model (List<String> contents) {
        this.contents = contents;
        this.aMap = parseModel();
        
    }
    
    /** z3
     *  (define-fun c () Int    1)
     [java]
     [java]
     [java]   (define-fun b () Int    1)
     [java]
     [java]
     [java]   (define-fun a () Int    1)
     [java]
     [java]
     [java]   (define-fun d () Int    (- 3))
     * @return
     */
    
    /** cvc4
     * 
     *     [java] (model
     [java] (define-fun a () Int 1)
     [java] (define-fun b () Int 1)
     [java] (define-fun c () Int 1)
     [java] (define-fun d () Int (- 3))
     [java] )
     * 
     * @return
     */
    
    
    /**
     *  (model
     [java]   ;; universe for SetInt:
     [java]   ;;   SetInt!val!2 SetInt!val!4 SetInt!val!1 SetInt!val!0 SetInt!va                                                                                                                                                     l!3
     [java]   ;; -----------
     [java]   ;; definitions for universe elements:
     [java]   (declare-fun SetInt!val!2 () SetInt)
     [java]   (declare-fun SetInt!val!4 () SetInt)
     [java]   (declare-fun SetInt!val!1 () SetInt)
     [java]   (declare-fun SetInt!val!0 () SetInt)
     [java]   (declare-fun SetInt!val!3 () SetInt)
     [java]   ;; cardinality constraint:
     [java]   (forall ((x SetInt))
     [java]           (or (= x SetInt!val!2)
     [java]               (= x SetInt!val!4)
     [java]               (= x SetInt!val!1)
     [java]               (= x SetInt!val!0)
     [java]               (= x SetInt!val!3)))
     [java]   ;; -----------
     [java]   (define-fun setEmptyInt () SetInt
     [java]     SetInt!val!0)
     [java]   (define-fun s2 () SetInt
     [java]     SetInt!val!2)
     [java]   (define-fun s1 () SetInt
     [java]     SetInt!val!1)
     [java]   (define-fun inSetInt ((x!0 SetInt) (x!1 Int)) Bool
     [java]     true)
     [java]   (define-fun setInsertInt ((x!0 SetInt) (x!1 Int)) SetInt
     [java]     SetInt!val!4)
     [java]   (define-fun setcardInt!16 ((x!0 SetInt)) Int
     [java]     (ite (= x!0 SetInt!val!0) 0
     [java]     (ite (= x!0 SetInt!val!2) 6
     [java]       1)))
     [java]   (define-fun k!15 ((x!0 SetInt)) SetInt
     [java]     (ite (= x!0 SetInt!val!0) SetInt!val!0
     [java]     (ite (= x!0 SetInt!val!2) SetInt!val!2
     [java]     (ite (= x!0 SetInt!val!4) SetInt!val!4
     [java]     (ite (= x!0 SetInt!val!1) SetInt!val!1
     [java]       SetInt!val!3)))))
     [java]   (define-fun setcardInt ((x!0 SetInt)) Int
     [java]     (setcardInt!16 (k!15 x!0)))
     [java]   (define-fun unionInt ((x!0 SetInt) (x!1 SetInt)) SetInt
     [java]     SetInt!val!3)
     [java] )

     * @return
     */
    private Map<String,String> parseModel() {
        System.out.println();
        HashMap<String, String> m = new HashMap<>();
        for (String d : contents) {
            String line = d.trim();
            if (line.startsWith(DECL)) {
                System.out.println("Decl: " + line);
            }
            
            if (line.startsWith(DEF)) {
                System.out.println("Def: " + line);
            }
//            System.out.println();
//            System.out.println(d);
//            System.out.println();
//            
           
//            Matcher matcher = defFun.matcher(d);
//            while(matcher.find()) {
//                System.out.println("Found " + matcher.group(0));
//            }
//            //d = d.replace("(define-fun", "").trim();
            //System.out.println("D: " + d);
 //           String[] parts = d.split(" ");
//            if (parts.length > 1) //cvc4
//                System.out.println("NAME " + parts[1]);
//            for (String p : parts) {
//                System.out.println("P " + p);
//               
//            }
        }
        return m;
    }
    @Override
    public String toString() {
        
//        for (String s : contents) {
//            System.out.println();
//            System.out.println(s);
//            System.out.println();
//        }
        return contents.toString();
    }
    
    private String getAssignment(String name) {
        return aMap.get(name);
        
    }
}
