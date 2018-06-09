package edu.kit.iti.algover.smttrans.data;

import java.util.LinkedHashSet;
import java.util.List;
import edu.kit.iti.algover.smttrans.translate.ConstDependency;
import edu.kit.iti.algover.smttrans.translate.Dependency;
import edu.kit.iti.algover.smttrans.translate.SMTTerm;

public class SMTContainer {

    private static final String DIVIDER = "=================================";
    private List<SMTTerm> antecedent;
    private List<SMTTerm> succedent;
    private LinkedHashSet<Dependency> dependencies = new LinkedHashSet<>();

    public SMTContainer(List<SMTTerm> a, List<SMTTerm> s) {
        this.antecedent = a;
        this.succedent = s;
        for (SMTTerm t : a) {
            this.dependencies.addAll(t.getDependencies());
        }
        for (SMTTerm t : s) {

            this.dependencies.addAll(t.getDependencies());

        }
    }

    public String toSMT() {
        StringBuilder sb = new StringBuilder();

        sb.append(instantiateDep());
        antecedent.forEach(t -> sb.append(t.toSMT()));
        succedent.forEach(s -> sb.append(s.toSMT())); // negate
        return sb.toString();
    }
    
    public String toPSMT() {
        StringBuilder sb = new StringBuilder();
        sb.append(declareDep());
        antecedent.forEach(t -> sb.append(t.toSMT()));
        succedent.forEach(s -> sb.append(s.toSMT())); // negate
        return sb.toString();
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
