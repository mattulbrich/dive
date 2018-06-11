package edu.kit.iti.algover.smttrans.data;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import edu.kit.iti.algover.term.FunctionSymbol;

public class AxiomContainer {

    private static final Pattern typeVars = Pattern.compile("(?<=par.)\\((.*?)\\)");

    static {

    }

    public static String instantiateAxiom(Axiom a, FunctionSymbol t) {
        return typeAxiom(a.getSmt(), t);
    }

    private static String typeAxiom(String axiom, FunctionSymbol type) {
        
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

        int i = 0;
        
        
        for (String t : typeVariables) {
            
        //    String pre = "(" + type.getTypeData().get(0)+ " " + t + ")";
         //7   axiom = axiom.replace(pre, type.toString()); //TODO regex ?
          //  axiom = axiom.replace(t,type.pop().toString());
            
        }

        return axiom;

    }

    public static List<String> instantiateSort(OperationType optype, FunctionSymbol t) {
        ArrayList<String> sorts = new ArrayList<>();
        if(t.getArity() > 1) //not built in 
            sorts.add("(declare-sort " + t.toString() + ")");
        for (String o : optype.getDependencies()) {
            sorts.add(o);
        }
        return sorts;
    }

    public static String declareAxiom(Axiom a, FunctionSymbol t) {
        String r = "(inst-ax :: " + a.name() + " :: " + t.toString() + ")";
        return r;
    }

    public static List<String> declareSort(OperationType optype, FunctionSymbol t) {
        ArrayList<String> sorts = new ArrayList<>();
        if(t.getArity() > 1) //not built in 
            sorts.add("(inst-sort :: " + t.toString() + ")");
        for (String o : optype.getDependenciesDecl()) {
            sorts.add(o);
        }
        return sorts;
    }

}
