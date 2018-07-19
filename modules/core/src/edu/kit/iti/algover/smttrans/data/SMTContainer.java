package edu.kit.iti.algover.smttrans.data;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import edu.kit.iti.algover.smttrans.translate.Dependency;
import edu.kit.iti.algover.smttrans.translate.SMTTerm;
import edu.kit.iti.algover.smttrans.translate.TypeContext;

public class SMTContainer {

    private static final String DIVIDER = "=================================";
    private List<SMTTerm> antecedent;
    private List<SMTTerm> succedent;
    private Set<Dependency> dependencies;

    public SMTContainer(List<SMTTerm> a, List<SMTTerm> s) {
        this.antecedent = a;
        this.succedent = s;
        this.dependencies = TypeContext.getDependencies();

    }

    private static String cleanUp(String ax) {
        int balance = 0;
        for (int i = 0; i < ax.length(); i++) {
            Character c = ax.charAt(i);
            if (c.equals('(')) {
                balance--;
            } if (c.equals(')')) {
                balance++;
            }
        }
        
        return ax.substring(0, ax.length()-balance);
    }
    public String toSMT() {
        StringBuilder sb = new StringBuilder();

        sb.append(instantiateDep());
        antecedent.forEach(t -> sb.append(cleanUp(t.toSMT(false))));
        succedent.forEach(s -> sb.append(cleanUp(s.toSMT(true)))); // negate
    
        String r = cleanUp(sb.toString());
        
        r = TypeContext.addFunctions(r);
        if (r.contains("Object"))  //TODO better version
            return TypeContext.addCasts(r);
        
        return r;
    }

    public String toPSMT() {
        StringBuilder sb = new StringBuilder();
        sb.append(declareDep());
        antecedent.forEach(t -> sb.append(cleanUp(t.toSMT(false))));
        succedent.forEach(s -> sb.append(cleanUp(s.toSMT(true)))); // negate
        
        String r = cleanUp(sb.toString());
        r = TypeContext.addFunctions(r);
        if (r.contains("Object"))  //TODO better version
            return TypeContext.addCasts(r);
        
        return cleanUp(sb.toString());
    }

    private String declareDep() {

        LinkedHashSet<String> sorts = new LinkedHashSet<>();
        LinkedHashSet<String> constants = new LinkedHashSet<>();
        LinkedHashSet<String> functions = new LinkedHashSet<>();
        LinkedHashSet<String> axioms = new LinkedHashSet<>();

        for (Dependency d : dependencies) {
            LinkedHashSet<String> set = d.declare();

            for (String s : set) {
                if (s.startsWith("(inst-sort")) {
                    sorts.add(s);
                    continue;
                } else if (s.startsWith("(inst-const")) {
                    constants.add(s);
                    continue;
                } else if (s.startsWith("(inst-fun") || s.startsWith("(define-fun")) { 
                    functions.add(s);
                    continue;

                } else {
                    axioms.add(s);
                }

            }

        }

        StringBuilder sb = new StringBuilder();
        sorts.forEach(s -> sb.append(s + "\r\n"));
        constants.forEach(c -> sb.append(c + "\r\n"));
        functions.forEach(f -> sb.append(f + "\r\n"));
        axioms.forEach(a -> sb.append(a + "\r\n"));
        sb.append(DIVIDER);
        return sb.toString();

    }

    private String instantiateDep() {

        LinkedHashSet<String> sorts = new LinkedHashSet<>();
        LinkedHashSet<String> constants = new LinkedHashSet<>();
        LinkedHashSet<String> functions = new LinkedHashSet<>();
        LinkedHashSet<String> axioms = new LinkedHashSet<>();

        for (Dependency d : dependencies) {
            LinkedHashSet<String> set = d.instantiate();
            for (String s : set) {
                if (s.startsWith("(declare-sort")) {
                    sorts.add(s);
                    continue;
                } else if (s.startsWith("(declare-const")) {
                    constants.add(s);
                    continue;

                } else if (s.startsWith("(declare-fun") || s.startsWith("(define-fun")) {
                    functions.add(s);
                    continue;

                } else {
                    axioms.add(s);
                }
            }

        }

        StringBuilder sb = new StringBuilder();
        sorts.forEach(s -> sb.append(s + "\r\n"));
        constants.forEach(c -> sb.append(c + "\r\n"));
        functions.forEach(f -> sb.append(f + "\r\n"));
        axioms.forEach(a -> sb.append(a + "\r\n"));

        return sb.toString();

    }

}
