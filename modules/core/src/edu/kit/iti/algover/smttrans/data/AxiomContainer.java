package edu.kit.iti.algover.smttrans.data;

import java.util.ArrayList;

import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import edu.kit.iti.algover.smttrans.translate.Type;

public class AxiomContainer {

    private static Map<Axiom, String> axioms = new HashMap<>();
    private static Map<OperationType, String> sorts = new HashMap<>();

    private static final Pattern typeVars = Pattern.compile("(?<=par.)\\((.*?)\\)");

    static {

        String setInst = "(define-sort Set (T) (Array T Bool))";
        String seqqInst = "";
        String mSetInst = "";
        String heapInst = "";

        sorts.put(OperationType.ARR, "");
        sorts.put(OperationType.ARR2, "");
        sorts.put(OperationType.SEQ, "");
        sorts.put(OperationType.SET, "");
        sorts.put(OperationType.MULTISET, "");

        String set1 = "(assert (par (T)\r\n" + "(forall\r\n" + "(\r\n" + "    (s1 (Set T))\r\n" + "    (s2 (Set T))\r\n"
                + "    (t T)\r\n" + ")\r\n" + "    (! \r\n" + "        (= (select (unionT s1 s2) t)\r\n"
                + "        (or (select s1 t) (select s2 t))) \r\n" + "        :pattern (( select (unionT s1 s2) t))\r\n"
                + "    ) \r\n" + ")))";
        axioms.put(Axiom.SET_1, set1);
    }

    public static String instantiateAxiom(Axiom a, Type t) {
        return typeAxiom(axioms.get(a), t);
    }

    private static String typeAxiom(String axiom, Type type) {

        // System.out.println("AX: " + axiom);
        // System.out.println("TYPE: " + type.toString());
        List<String> typeVariables = new ArrayList<String>();

        // remove par, TV
        Matcher matcher = typeVars.matcher(axiom);
        if (matcher.find()) {
            String[] tvs = matcher.group(1).split(" ");
            for (String s : tvs) {
                typeVariables.add(s);
                axiom = axiom.replaceFirst(s, "");
            }

        }

        axiom = axiom.replaceFirst("\\(par \\(", "");
        axiom = axiom.replaceFirst("\\)", "");
        int i = 0;
        for (String t : typeVariables) {
            // axiom = axiom.replaceAll(t, types.get(i)); // TODO type for multiple tv
            // i++;
            axiom = axiom.replaceAll(t, type.toString());
        }

     //   System.out.println(axiom);
        return axiom;

    }

    public static List<String> instantiateSort(OperationType type, Type t) {
        // TODO Auto-generated method stub
        List<String> l = new ArrayList<>();
        String s = sorts.getOrDefault(type, t.toString()); // TODO sort
        l.add("(declare-sort " + s + ")");
        return l;
    }

}
