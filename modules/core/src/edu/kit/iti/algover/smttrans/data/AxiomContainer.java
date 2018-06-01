package edu.kit.iti.algover.smttrans.data;

import java.util.ArrayList;

import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;


public class AxiomContainer {

    private static Map<Axiom, String> axioms = new HashMap<>();
   
    private static final Pattern typeVars = Pattern.compile("(?<=par.)\\((.*?)\\)");

    static {
        String set1 = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s1 (Set T))\r\n" + "    (s2 (Set T))\r\n"
                + "    (t T)\r\n" + ")\r\n" + "    (! \r\n" + "        (= (select (unionT s1 s2) t)\r\n"
                + "        (or (select s1 t) (select s2 t))) \r\n" + "        :pattern (( select (unionT s1 s2) t))\r\n"
                + "    ) \r\n" + ")))";
        axioms.put(Axiom.SET_1, set1);
    }

    public static List<String> instantiateAxioms(Map<List<String>, LinkedHashSet<Operation>> ax) {
        List<String> typedAxioms = new ArrayList<>();
        for (List<String> type : ax.keySet()) {
            // System.out.println("TYPE: " + type);
            //debug
            typeAxiom(axioms.get(Axiom.SET_1), new ArrayList<String>());
            //debug
            for (Operation op : ax.get(type)) {
                // System.out.println("NAME " + op.name());
            //    for (Axiom i : op.getInstantiations()) {
             //       typedAxioms.add(typeAxiom(axioms.get(i), type));

               // }
            }

        }

        return typedAxioms;

    }

    private static String typeAxiom(String axiom, List<String> types) {

        List<String> typeVariables = new ArrayList<String>(); // regex for TV
        // (par (T V))

        //remove par, TV
        Matcher matcher = typeVars.matcher(axiom);
        if (matcher.find()) {
            String[] tvs = matcher.group(1).split(" ");
            for (String s : tvs) {
             //   System.err.println(s);
            }

    }
 
        int i = 0;
        for (String t : typeVariables) {
            axiom = axiom.replaceAll(t, types.get(i));
            i++;
        }

      //  System.out.println();

        return null;

    }

}
