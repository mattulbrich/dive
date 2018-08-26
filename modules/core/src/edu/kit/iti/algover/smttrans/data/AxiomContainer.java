package edu.kit.iti.algover.smttrans.data;

import java.util.ArrayList;

import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.StringTokenizer;
import java.util.regex.Pattern;

import edu.kit.iti.algover.smttrans.translate.TypeContext;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.util.Pair;

public class AxiomContainer {
    private static Set<Pair<List<String>, FunctionSymbol>> sorts = new LinkedHashSet<>();

    private static final Pattern openPar = Pattern.compile("\\(");

    static {
        AxiomLoader.load();
    }

    public static void reset() {
        sorts.clear();
    }

    public static String crossType(List<String> t1, List<String> t2) {
        List<String> types = t2.subList(1, t2.size());
        // Axiom a1 = Axiom.valueOf(t1.get(0)).getComplement(types);
        // return typeAxiom(a1.smt, types);
        return "";
    }

    public static List<String> crossProduct() {
        List<String> axioms = new ArrayList<>();
        Set<List<String>> types = new LinkedHashSet<>();
        for (Pair<List<String>, FunctionSymbol> p : sorts) {
            types.add(p.fst);
        }
        System.out.println("===");
        System.out.println(types);
        // TODO cross product, multiple arrselects ?
        for (List<String> t1 : types) {
            for (List<String> t2 : types) {
                if (t1.equals(t2))
                    continue;
                axioms.add(crossType(t1, t2));
            }
        }

        return axioms;
    }

    private static void addType(Axiom a, FunctionSymbol t) {

        List<String> l = new ArrayList<>();
        if (a.equals(Axiom.FIELDSELECT) || a.equals(Axiom.FIELDSTORE))
            return;
        if (!a.isMultiTyped() && !a.equals(Axiom.A11) && !a.equals(Axiom.A21))
            return;

        l.add(a.name());
        // l.add(TypeContext.SMT_ARRNAME);
        l.addAll(TypeContext.getTypeArguments(t.getName()));
        sorts.add(new Pair<List<String>, FunctionSymbol>(l, t));

    }

    private static Set<String> handleAnon() {
        Set<String> ax = new LinkedHashSet<>(Arrays.asList(Axiom.ANON.smt));
        for (Pair<List<String>, FunctionSymbol> s : sorts) {
            Axiom a = Axiom.H9;

            if (s.fst.get(0).equals(TypeContext.SMT_ARR2NAME)) {
                a = Axiom.H11;
            } else if (s.fst.get(0).equals(TypeContext.SMT_ARRNAME)) {
                a = Axiom.H10;
            }
            ax.add(typeAxiom(a.smt, s.snd));
        }

        return ax;

    }

    public static Set<String> instantiateAxiom(Axiom a, FunctionSymbol t) {

        addType(a, t);
        if (a.equals(Axiom.ANON))
            return handleAnon();

        return new HashSet<>(Arrays.asList(typeAxiom(a.getSmt(), t)));

    }

    private static String removeParantheses(String ax) {

        if (ax.startsWith("(assert")) {

            return ax.substring(0, ax.length() - 1);
        }

        if (ax.startsWith("(declare-")) {
            StringBuilder sb = new StringBuilder("(");
            String r = ax.substring(1).replaceFirst(openPar.pattern(), "").trim();
            sb.append(r.substring(0, r.length() - 2));
            return sb.toString();
        }
        return ax;

    }

    public static Pair<List<String>, String> prepare(String axiom) {

        String ax = "";
        String tv = "";

        if (!axiom.contains("(par"))
            return new Pair<>(new ArrayList<>(), axiom);
        StringTokenizer tokenizer = new StringTokenizer(axiom, "(", true);
        while (tokenizer.hasMoreTokens()) {
            String token = tokenizer.nextToken();
            String t = token.trim();
            if (t.equals("par")) {
                tokenizer.nextToken();
                String ct = tokenizer.nextToken().replace(")", ""); // first tv
                tv += ct;
                ct = tokenizer.nextToken().trim();
                while (!ct.equals("(")) { // multiple tv
                    tv += " " + ct;
                    ct = tokenizer.nextToken().trim();
                }
                token = tokenizer.nextToken();
            }

            ax += token;

        }

        List<String> r = new ArrayList<>();
        for (String t : tv.split(" ")) {
            r.add(t.trim());
        }

        return new Pair<List<String>, String>(r, removeParantheses(ax));

    }

    private static String typeAxiom(String axiom, List<String> types) {
        Pair<List<String>, String> p = prepare(axiom);
        List<String> tvs = p.fst;

        String ax = p.snd;

        for (int i = 0; i < tvs.size(); i++) {
            ax = ax.replace(tvs.get(i), types.get(i));
        }

        return ax;
    }

    private static String typeAxiom(String axiom, FunctionSymbol type) {
        Pair<List<String>, String> p = prepare(axiom);
        List<String> tvs = p.fst;
        List<String> types = TypeContext.getTypeArguments(type.getName());

        String ax = p.snd;
        if (types.size() != tvs.size()) { //TODO anon error
            return "";
        }
        for (int i = 0; i < tvs.size(); i++) {
            ax = ax.replace(tvs.get(i), types.get(i));
        }

        return ax;
    }

    private static boolean isApplicable(String axiom, Sort sort) {

        if (!axiom.contains("(par"))
            return false;
        String name = TypeContext.normalizeName(sort.getName());

        if (!axiom.contains(name + "<"))
            return false;

        Pair<List<String>, String> p = prepare(axiom);
        List<String> tvs = p.fst;
        if (tvs.size() != sort.getArguments().size()) {

            return false;
        }
        return true;

    }

    public static List<String> instantiateSort(FunctionSymbol t) {

        ArrayList<String> sorts = new ArrayList<>();

        for (Sort s : t.getArgumentSorts()) {

            if (!TypeContext.isBuiltIn(s.getName())) {

                sorts.add("(declare-sort " + TypeContext.normalizeSort(s.getName(), s.toString()) + " 0)");
            }

        }

        if (!TypeContext.isBuiltIn(t.getResultSort().getName())) {
            // System.out.println("SORT2 " + t.toString());
            sorts.add("(declare-sort " + TypeContext.normalizeReturnSort(t) + " 0)");
        }

        return sorts;
    }

    public static String declareAxiom(Axiom a, FunctionSymbol t) {
        System.out.println(a.name());
        String r = "";
        for (Sort s : t.getArgumentSorts()) {
            if (isApplicable(a.getSmt(), s)) {

                r += a.getSmt() + " :: " + TypeContext.normalizeSort(s.getName(), s.toString()) + "\r\n";
            }
        }
        return r;
    }

    public static List<String> declareSort(FunctionSymbol t) {
        ArrayList<String> sorts = new ArrayList<>();

        for (Sort s : t.getArgumentSorts()) {

            if (!TypeContext.isBuiltIn(s.getName())) {
                sorts.add("(inst-sort :: " + TypeContext.normalizeSort(s.getName(), s.toString()) + ")");
            }

        }

        return sorts;
    }

}
