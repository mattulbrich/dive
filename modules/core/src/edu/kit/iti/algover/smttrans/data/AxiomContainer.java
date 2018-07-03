package edu.kit.iti.algover.smttrans.data;

import java.util.ArrayList;

import java.util.List;
import java.util.StringTokenizer;
import java.util.regex.Pattern;
import edu.kit.iti.algover.smttrans.translate.TypeContext;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.util.Pair;

public class AxiomContainer {

    private static final Pattern openPar = Pattern.compile("\\(");

    static {

    }

    public static String instantiateAxiom(Axiom a, FunctionSymbol t) {

        return typeAxiom(a.getSmt(), t);

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

    private static Pair<List<String>, String> prepare(String axiom) {
        ;
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

    private static String typeAxiom(String axiom, FunctionSymbol type) {
        Pair<List<String>, String> p = prepare(axiom);
        List<String> tvs = p.fst;
        List<String> types = TypeContext.getTypeArguments(type.getName());

        String ax = p.snd;

        for (int i = 0; i < tvs.size(); i++) {
            ax = ax.replace(tvs.get(i), types.get(i));
        }

        return ax;
    }

    private static boolean isApplicable(String axiom, Sort sort) {

        if (!axiom.contains("(par"))
            return false;
        Pair<List<String>, String> p = prepare(axiom);
        List<String> tvs = p.fst;
        if (tvs.size() != TypeContext.normalizeName(sort.getName()).split("\\.").length)
            return false;

        return true;

    }

    public static List<String> instantiateSort(FunctionSymbol t) {

        ArrayList<String> sorts = new ArrayList<>();

        for (Sort s : t.getArgumentSorts()) {

            if (!TypeContext.isBuiltIn(s.getName())) {
                //System.out.println("SORT1 " + s.toString());
                
                //String r = addTypeArguments(normalizeSort(fs.getResultSort().getName()), getTypeArguments(fs.toString())); 
                
                sorts.add("(declare-sort " + TypeContext.normalizeSort(s.getName(), s.toString()) + " 0)");
            }

        }

        if (!TypeContext.isBuiltIn(t.getResultSort().getName())) {
            //System.out.println("SORT2 " + t.toString());
            sorts.add("(declare-sort " + TypeContext.normalizeReturnSort(t) + " 0)");
        }

        return sorts;
    }

    public static String declareAxiom(Axiom a, FunctionSymbol t) {

        String r = "";
        for (Sort s : t.getArgumentSorts()) {
            if (isApplicable(a.getSmt(), s)) {
                r += a.getSmt() + " :: " + TypeContext.normalizeName(s.getName()) + "\r\n";
            }
        }
        return r;
    }

    public static List<String> declareSort(FunctionSymbol t) {
        ArrayList<String> sorts = new ArrayList<>();

        for (Sort s : t.getArgumentSorts()) {

            if (!TypeContext.isBuiltIn(s.getName())) {
                sorts.add("(inst-sort :: " + TypeContext.normalizeName(s.getName()) + ")");
            }

        }

        return sorts;
    }

}
