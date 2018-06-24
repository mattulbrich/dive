package edu.kit.iti.algover.smttrans.access;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.StringTokenizer;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;

import edu.kit.iti.algover.smttrans.translate.Names;
import edu.kit.iti.algover.smttrans.translate.TypeContext;

public class Model {

    // private static Pattern defFun = Pattern.compile("\\(define-fun(.*?)\\)");

    
    private List<String> contents;
    private BiMap<String, String> vars;
    private List<List<String>> assignments;
    private static final String DECL = "declare-fun";
    private static final String DEF = "define-fun";
    private static final String PRE = Names.getPrefix();
    private static final String ITE = "(ite";
    private static final String VAL = "val";
    private static final String DEFAULT = "default";

    public Model(List<String> contents) {
        this.contents = contents;
        //this.vars = parseVars();
      //  this.assignments = parseModel(parseFuncs(contents));
        parseVars();
        

//        System.out.println(parseVars().toString());
//        System.out.println(parseFuncs(contents).toString());
//        parseModel(parseFuncs(contents));
//        printAssignments();
    }

    
    private void printAssignments() {
    
        
        Set<String> namedVars = vars.keySet(); //TODO
        
        System.out.println("=== Model ===");
    
    
        for (List<String> a : assignments) {
          //  System.out.println("a " + a);
            StringBuilder sb = new StringBuilder();
            sb.append(a.get(0).split("!")[0]);
            sb.append("(");
            String var = vars.inverse().getOrDefault(a.get(1), a.get(1));
            sb.append(var);
            sb.append(")");
            sb.append(" = ");
            sb.append(a.get(2));
            System.out.println(sb.toString());
            
            
        }
        
        System.out.println("=== ===");
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
 
            for (int i = 0; i < a.size() - 1; i+=2) {
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
                c.add(a.get(a.size()-1));
                funcAssignments.add(c);
            }
         
           
        }
     //   System.out.println(funcAssignments.toString());
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

    private List<List<String>> parseVars() {
        //BiMap<String, String> subs = HashBiMap.create();

        List<List<String>> vars = new ArrayList<>();
        for (String d : contents) {
            String line = d.trim().replaceAll(" +", " ");
            line = line.substring(1,line.length()-1);
//            if(line.startsWith(";"))
//                continue;
            // System.out.println();
            // System.out.println(line);
            // System.out.println();
//            System.out.println("L " + line);
            if (line.startsWith(DECL)) {
                List<String> parts = Arrays.asList(line.split("(?<![\\(,\\)])\\s+"));
                    System.out.println(parts.toString());
                List<String> decl = new ArrayList<>();
                decl.add("Decl: ");
                decl.addAll(parts.subList(1,parts.size()));
                vars.add(decl);
                continue;
            }
            
            if (line.startsWith(DEF)) {
                List<String> parts = Arrays.asList(line.split("(?<![\\(,\\)])\\s+"));
                    System.out.println(parts.toString());
                List<String> decl = new ArrayList<>();
                decl.add("Def: ");
                decl.addAll(parts.subList(1,parts.size()));
                vars.add(decl);
                continue;
            }
            
            

//               
//
//                String k = "";
//                String v = "";
//                for (String p : parts) {
//
//                    if (p.contains(PRE)) {
//                        k = p;
//                        continue;
//                    }
//                    if (p.contains(VAL)) {
//                        v = p;
//                        continue;
//                    }
//                }
//
//                subs.put(k, v.substring(0, v.length() - 1));
//            }
//
//        }

        }
//
//        System.out.println(subs.toString());
        System.out.println("Vars " + vars.toString());
        return vars;
    }

    @Override
    public String toString() {

        return contents.toString();
    }

}
