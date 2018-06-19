package edu.kit.iti.algover.smttrans.data;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.StringTokenizer;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collector;
import java.util.stream.Collectors;

import edu.kit.iti.algover.smttrans.translate.TypeContext;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.util.Pair;

public class AxiomContainer {

    private static final Pattern typeVars = Pattern.compile("(?<=par.)\\((.*?)\\)");
    private static final Pattern openPar = Pattern.compile("\\(");

    static {

    }

    public static String instantiateAxiom(Axiom a, FunctionSymbol t) {
        
   
                return typeAxiom(a.getSmt(), t);
       
            
    }

    private static String removeParantheses(String ax) {
        
        
        if (ax.startsWith("(assert")) {

            return ax.substring(0, ax.length()-1);
        }
        
        if (ax.startsWith("(declare-")) {
            StringBuilder sb = new StringBuilder("(");
            String r = ax.substring(1).replaceFirst(openPar.pattern(), "").trim();
            sb.append(r.substring(0, r.length()-2));
            return sb.toString();
        }
        return ax;

    }

    private static Pair<List<String>, String> prepare(String axiom) {
;
        String ax = "";
        String tv = "";


        StringTokenizer tokenizer = new StringTokenizer(axiom, "(",true);
        while (tokenizer.hasMoreTokens()) {
            String token = tokenizer.nextToken();
            String t = token.trim();
            if (t.equals("par")) {
                tokenizer.nextToken();
                String ct = tokenizer.nextToken().replace(")",""); //first tv
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
      //  System.out.println("Axiom " + axiom);
      //  System.out.println("Type " + type.toString());
        Pair<List<String>, String> p = prepare(axiom);
        List<String> tvs = p.fst;
        List<String> types = TypeContext.getFuncArguments(type);
     //  types = TypeContext.getSubTypes(type);
      
        String ax = p.snd;
     //    System.out.println("TV " + tvs);
     //    System.out.println("Types " + types);

        for (int i = 0; i < tvs.size(); i++) {
            ax = ax.replace(tvs.get(i), types.get(i));
        }

        return ax;
    }



    private static boolean isApplicable(String axiom, Sort sort) {

        List<String> typeVariables = new ArrayList<String>();

        // remove par, TV
        Matcher matcher = typeVars.matcher(axiom);
        if (matcher.find()) {
            String[] tvs = matcher.group(1).split(" ");
            for (String s : tvs) {
                typeVariables.add(s);
                axiom = axiom.replaceFirst(s, "");
            }
            axiom = axiom.replaceFirst("\\(par \\(", "");
            axiom = axiom.replaceFirst("\\)", "");
        }

        List<String> subtypes = TypeContext.getSubTypes(sort);

        for (String t : typeVariables) {

            for (String ty : subtypes) {

                String pre = "(" + ty + " " + t + ")";
                if (axiom.contains(pre)) {
                    return true;
                }

            }
        }

        return false;
    }

    public static List<String> instantiateSort(FunctionSymbol t) {

        ArrayList<String> sorts = new ArrayList<>();

        for (Sort s : t.getArgumentSorts()) {

            if (!TypeContext.isBuiltIn(s)) {
                sorts.add("(declare-sort " + TypeContext.normalizeSort(s) + " 0)");
            }

        }

        if (!TypeContext.isBuiltIn(t.getResultSort())) {
            sorts.add("(declare-sort " + TypeContext.normalizeSort(t.getResultSort()) + " 0)");
        }

        return sorts;
    }

    public static String declareAxiom(Axiom a, FunctionSymbol t) {

        String r = "";
        for (Sort s : t.getArgumentSorts()) {
            if (isApplicable(a.getSmt(), s)) {
                r += a.getSmt() + " :: " + TypeContext.normalizeSort(s);
            }
        }
        return r;
    }

    public static List<String> declareSort(FunctionSymbol t) {
        ArrayList<String> sorts = new ArrayList<>();

        for (Sort s : t.getArgumentSorts()) {

            if (!TypeContext.isBuiltIn(s)) {
                sorts.add("(inst-sort :: " + TypeContext.normalizeSort(s) + ")");
            }

        }
        if (!TypeContext.isBuiltIn(t.getResultSort())) {
            sorts.add("(declare-sort " + TypeContext.normalizeSort(t.getResultSort()) + " 0)");
        }
        return sorts;
    }

}
