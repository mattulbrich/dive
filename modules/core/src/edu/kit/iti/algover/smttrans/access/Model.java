package edu.kit.iti.algover.smttrans.access;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.StringTokenizer;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;

import edu.kit.iti.algover.smttrans.translate.Names;
import edu.kit.iti.algover.smttrans.translate.TypeContext;
import edu.kit.iti.algover.util.Pair;

public class Model {

    // private static Pattern defFun = Pattern.compile("\\(define-fun(.*?)\\)");

    private List<String> contents;
    private List<List<String>> vars;
    private List<List<String>> assignments;
    private BiMap<String, String> vMap = HashBiMap.create();
    private static final String DECL = "declare-fun";
    private static final String DEF = "define-fun";
    private static final String PRE = Names.getPrefix();
    private static final String ITE = "(ite";
    private static final String VAL = "val";
    private static final String DEFAULT = "default";

    public Model(List<String> contents) {
        this.contents = contents;
        // this.vars = parseVars();
        // this.assignments = parseModel(parseFuncs(contents));

        // printVars();
        this.vars = subVars(parseVars(parseModel()));
        printVars();
    }

    private List<String> sub(List<String> vars) {
        List<String> r = new ArrayList<>();
        for (String s : vars) {
            for (String sub : vMap.values()) {
                s = s.replace(sub, vMap.inverse().get(sub));
            }

            r.add(s.replace("() ", ": "));
        }
        if (r.get(1).equals(r.get(r.size() - 1)))
            return new ArrayList<>();
        return r;
    }

    private List<List<String>> subVars(Pair<List<List<String>>, List<List<String>>> vars) {
        List<List<String>> decl = new ArrayList<>();
        List<List<String>> def = new ArrayList<>();

        for (List<String> de : vars.fst) {
            decl.add(sub(de));
        }
        for (List<String> de : vars.snd) {
            de = sub(de);
            if (!de.isEmpty())
                def.add(sub(de));
        }
        // System.out.println("Dec " + decl);
        // System.out.println("Def " + def);
        // for (List<String> d1 : def) {
        // System.out.println("IN " + d1);
        // System.out.println("OUT " + parseModel(d1));
        // }
        decl.addAll(def);
        return decl;

    }

    private List<List<String>> parseModel(List<String> model) {
        List<String> a = new ArrayList<>();
        List<List<String>> funcAssignments = new ArrayList<>();
        String func = "";
        for (String line : model) {
            line = line.replace("(", "").replace(")", "");
            StringTokenizer t = new StringTokenizer(line);
            func = t.nextToken();
            while (t.hasMoreTokens()) {

                String token = t.nextToken();
                if (!isRelevant(token)) {
                    continue;
                }
                a.add(token);

            }

            for (int i = 0; i < a.size() - 1; i += 2) {
                List<String> b = new ArrayList<>();
                b.add(func);
                b.add(a.get(i));
                b.add(a.get(i + 1));
                funcAssignments.add(b);
            }

            if (a.size() % 2 == 1) {
                List<String> c = new ArrayList<>();
                c.add(func);
                c.add(DEFAULT);
                c.add(a.get(a.size() - 1));
                funcAssignments.add(c);
            }

        }
        // System.out.println(funcAssignments.toString());
        return funcAssignments;

    }

    private List<String> parseFuncs(List<String> model) {
        List<String> nmodel = new ArrayList<>();
        for (String d : contents) {
            String line = d.trim();
            if (line.startsWith(DEF) && !line.contains(PRE)) {
                String[] parts = line.split("(?<![\\(,\\)])\\s+");
                String fsign = parts[1];
                if (fsign.contains("!")) {
                    StringBuilder sb = new StringBuilder(fsign);
                    int i = 0;
                    while (!parts[i].equals(ITE)) {
                        i++;
                    }
                    for (int j = i; j < parts.length; j++) {
                        sb.append(" " + parts[j]);
                    }
                    String r = sb.toString();
                    nmodel.add(r.substring(0, r.length() - 1));
                }

            }
        }
        return nmodel;
    }

    private Pair<List<List<String>>, List<List<String>>> parseVars(List<List<String>> vars) {
        List<List<String>> declaratations = new ArrayList<>();
        List<List<String>> definitions = new ArrayList<>();

        for (List<String> v : vars) {
            if (v.get(0).startsWith("Decl:")) {
                declaratations.add(v);
                continue;
            }

            if (v.get(0).startsWith("Def:") && v.get(1).startsWith(PRE)) {
                String key = v.get(1);
                String value = "";
                if (v.get(v.size() - 2).equals("(-"))
                    value += "-";
                value += v.get(v.size() - 1).replace(")", "");
                // vMap.put(v.get(1), v.get(v.size() - 1));

                vMap.put(key, value);
                continue;
            }

            for (String s : v) {
                if (s.startsWith("()")) {
                    vMap.put(v.get(1), v.get(v.size() - 1));
                    continue;
                }
            }
            definitions.add(v);
        }

        System.out.println("Declarations " + declaratations.toString());
        System.out.println(vMap.toString());
        return new Pair<List<List<String>>, List<List<String>>>(declaratations, definitions);
    }

    private boolean isRelevant(String s) {
        if (TypeContext.isNumeric(s.replace("(", "").replace(")", "")))
            return true;
        if (s.equals("(=") || s.equals(ITE))
            return false;
        int i = s.length();
        int j = s.replace("!", "").length();
        return (i - j) > 1;

    }

    private List<List<String>> parseModel() {
        // BiMap<String, String> subs = HashBiMap.create();

        List<List<String>> vars = new ArrayList<>();
        for (String d : contents) {
            String line = d.trim().replaceAll(" +", " ");
            line = line.substring(1, line.length() - 1);

            if (line.startsWith(DECL)) {
                List<String> parts = Arrays.asList(line.split("(?<![\\(,\\)])\\s+"));
                System.out.println(parts.toString());
                List<String> decl = new ArrayList<>();
                decl.add("Decl: ");
                decl.addAll(parts.subList(1, parts.size()));
                vars.add(decl);
                continue;
            }

            if (line.startsWith(DEF)) {
                List<String> parts = Arrays.asList(line.split("(?<![\\(,\\)])\\s+"));
                System.out.println(parts.toString());
                List<String> decl = new ArrayList<>();
                decl.add("Def: ");
                decl.addAll(parts.subList(1, parts.size()));
                vars.add(decl);
                continue;
            }

        }

        System.out.println("Vars " + vars.toString());
        return vars;
    }

    public void printVars() {
        System.out.println("=== Model ===");
        System.out.println();

        if (vars.isEmpty()) {

            for (String v : vMap.keySet()) {
                System.out.println("Def: " + v + " = " + vMap.get(v));
            }
        } else {

            for (List<String> v : vars) {
                String line = "";

                for (String l : v) {
                    line += " " + l;
                }

                System.out.println(line.trim());
            }
        }
        System.out.println();
        System.out.println("=== ===");

    }

    @Override
    public String toString() {

        return contents.toString();
    }

}
