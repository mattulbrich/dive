package edu.kit.iti.algover.smttrans.access;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class Model {

    private Map<String,String> aMap;
    private List<String> contents;
    public Model (List<String> contents) {
        this.contents = contents;
        this.aMap = parseModel();
        
    }
    
    /**
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
    
    private Map<String,String> parseModel() {
        HashMap<String, String> m = new HashMap<>();
        for (String d : contents) {
            //d = d.replace("(define-fun", "").trim();
            //System.out.println("D: " + d);
            String[] parts = d.split(" ");
            System.out.println("NAME " + parts[1]);
//            for (String p : parts) {
//                System.out.println("P " + p);
//               
//            }
        }
        return m;
    }
    @Override
    public String toString() {
        
        for (String s : contents) {
            System.out.println();
            System.out.println(s);
            System.out.println();
        }
        return contents.toString();
    }
    
    private String getAssignment(String name) {
        return aMap.get(name);
        
    }
}
