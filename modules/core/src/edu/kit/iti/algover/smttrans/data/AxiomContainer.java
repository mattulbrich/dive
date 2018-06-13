package edu.kit.iti.algover.smttrans.data;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collector;
import java.util.stream.Collectors;

import edu.kit.iti.algover.smttrans.translate.TypeContext;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;

public class AxiomContainer {

    private static final Pattern typeVars = Pattern.compile("(?<=par.)\\((.*?)\\)");

    static {

    }

    public static String instantiateAxiom(Axiom a, FunctionSymbol t) {
        return typeAxiom(a.getSmt(), t);
    }

    private static String removeParantheses(String ax) {
        StringBuilder sb = new StringBuilder(ax);
        List<Integer> open = new ArrayList<>();
        List<Integer> close = new ArrayList<>();
        for (int i = 0; i < ax.length(); i++) {
            char c = ax.charAt(i);
            if (c == '(') {
                open.add(i);
            }
            if (c == ')') {
                close.add(i);
            }

        }

        return ax.substring(0, open.get(1)) + ax.substring(open.get(1) + 1, close.get(close.size() - 1) - 1);
    }

    private static String typeAxiom(String axiom, FunctionSymbol type) {

        // System.out.println("AX: " + type.toString());

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

        List<List<String>> subtypes = TypeContext.getSubTypes(type.getArgumentSorts());

        if (typeVariables.size() == 1) {
            String t = typeVariables.get(0);

            for (List<String> ty : subtypes) {

                StringBuilder c = new StringBuilder();
                ty.forEach(c::append);

                String complete = c.toString();
                StringBuilder p = new StringBuilder();

                ty.subList(1, ty.size()).forEach(p::append);

                String pop = p.toString();
                for (String typ : ty) {

                    String pre = "(" + typ + " " + t + ")";
                    if (axiom.contains(pre)) { //TODO setemptyT
                        axiom = axiom.replace(pre, complete);
                        axiom = axiom.replace(t, pop);
                    }

                }
            }

        } else { // TODO better version (multiple TV)
 
            List<String> preambleTypes = new ArrayList<>();
            List<String> types = new ArrayList<>();

            for (List<String> st : subtypes) {
                if (!(st.size() > 1))
                    continue;
                for (String sst : st) {
                    if (!sst.contains(",")) {
                        preambleTypes.add(sst.substring(0, 1).toUpperCase() + sst.substring(1));
                    } else {
                        String[] parts = sst.split(",");
                        for (String p : parts) {
                            types.add(p.substring(0, 1).toUpperCase() + p.substring(1)); // TODO method
                        }
                    }
                }
            }
            
            StringBuilder psb = new StringBuilder("(");
            preambleTypes.forEach(psb::append);
           
            String preamble = psb.toString();
              StringBuilder sb = new StringBuilder(preamble);
              for  (String t : typeVariables) {
                  sb.append(" " + t);
              }
              sb.append(")");
             String pre = sb.toString();
             StringBuilder cb = new StringBuilder();
             preambleTypes.forEach(cb::append);
             
             for (String tString : types) {
                 cb.append(tString);
                 cb.append(".");
             }
  
             String complete = cb.toString().substring(0,cb.toString().length()-1); 
       
            
             axiom = axiom.replace(pre, complete);
            for (int i = 0; i < typeVariables.size(); i++) {
                String tv = typeVariables.get(i);
                String ty = types.get(i);

          
      
           
                axiom = axiom.replace(tv, ty);


            }
        }
        // System.out.println("AX: " + axiom);
        return removeParantheses(axiom);

    }

    public static List<String> instantiateSort(OperationType optype, FunctionSymbol t) {

        ArrayList<String> sorts = new ArrayList<>();

        for (Sort s : t.getArgumentSorts()) {

            if (!TypeContext.isBuiltIn(s)) {
                sorts.add("(declare-sort " + TypeContext.normalizeSort(s) + " 0)");
            }

        }

        for (String o : optype.getDependencies()) {
            sorts.add(o);
        }
        return sorts;
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

    public static String declareAxiom(Axiom a, FunctionSymbol t) {

        // TODO use Name ?
        String r = "";
        for (Sort s : t.getArgumentSorts()) {
            if (isApplicable(a.getSmt(), s)) {
                r += "(inst-ax :: " + a.name() + " :: " + TypeContext.normalizeSort(s) + ")";
            }
        }
        return r;
    }

    public static List<String> declareSort(OperationType optype, FunctionSymbol t) {
        ArrayList<String> sorts = new ArrayList<>();

        for (Sort s : t.getArgumentSorts()) {

            if (!TypeContext.isBuiltIn(s)) {
                sorts.add("(inst-sort :: " + TypeContext.normalizeSort(s) + ")");
            }
        }
        for (String o : optype.getDependencies()) {
            sorts.add(o);
        }
        return sorts;
        // ArrayList<String> sorts = new ArrayList<>();
        // if(t.getArity() > 1) //not built in
        // sorts.add("(inst-sort :: " + t.toString() + ")");
        // for (String o : optype.getDependenciesDecl()) {
        // sorts.add(o);
        // }
        // return sorts;
    }

}
