package edu.kit.iti.algover.smttrans.translate;

import java.text.DecimalFormatSymbols;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import com.google.common.base.CharMatcher;
import com.google.common.base.Splitter;
import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import com.google.common.collect.Iterables;

import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.smttrans.data.Operation;
import edu.kit.iti.algover.smttrans.data.OperationMatcher;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.util.Pair;

public class TypeContext {
    private static SymbolTable symbolTable = new MapSymbolTable(new HashSet<FunctionSymbol>());
    public static final String AV_ARRNAME = "array";
    public static final String SMT_ARRNAME = "Arr";
    public static final String AV_SETEMPTYNAME = "empty<object>";
    public static final String SMT_SETEMPTYNAME = "setEmptyObject";
    public static final String AV_ARR2NAME = "array2";
    public static final String SMT_ARR2NAME = "Arr2";
    public static final String AV_INTNAME = "int";
    public static final String SMT_INTNAME = "Int";
    public static final String AV_BOOLNAME = "bool";
    public static final String SMT_BOOLNAME = "Bool";
    public static final String AV_HEAPNAME = "heap";
    public static final String SMT_HEAPNAME = "Heap";
    public static final String AV_MODNAME = "$mod";
    public static final String AV_ANON = "$anon";
    public static final String AV_EVERYTHINGNAME = "$everything";
    public static final String AV_AHEAP = "$aheap";
    public static final String AV_DECR = "$decr";
    private static BiMap<String, String> nmap = HashBiMap.create();
    private static BiMap<String, String> smap = HashBiMap.create();
    private static List<Operation> specialOps = Arrays.asList(Operation.HEAP, Operation.AHEAP, // , Operation.ANON
            Operation.MOD, Operation.EVERYTHING, Operation.DECR);
    static {
        smap.put(AV_ARRNAME, SMT_ARRNAME);
        smap.put(AV_INTNAME, SMT_INTNAME);
        smap.put(AV_BOOLNAME, SMT_BOOLNAME);
        smap.put(AV_HEAPNAME, SMT_HEAPNAME);
        smap.put(AV_AHEAP, Operation.AHEAP.toSMT());
        smap.put(AV_DECR, Operation.DECR.toSMT());
        smap.put(AV_ARR2NAME, SMT_ARR2NAME);

        nmap.put(AV_MODNAME, Operation.MOD.toSMT());
        nmap.put(AV_SETEMPTYNAME, SMT_SETEMPTYNAME);
        nmap.put(AV_ARRNAME, SMT_ARRNAME);
        nmap.put(AV_ARR2NAME, SMT_ARR2NAME);
        nmap.put(AV_INTNAME, SMT_INTNAME);
        nmap.put(AV_BOOLNAME, SMT_BOOLNAME);
        nmap.put(AV_HEAPNAME, SMT_HEAPNAME);
        nmap.put(AV_AHEAP, Operation.AHEAP.toSMT());
        nmap.put(AV_DECR, Operation.DECR.toSMT());

    }

    public static BiMap<String, String> getDefaults() {
        return nmap;
    }

    public static boolean isBuiltIn(String name) {
        return name.equals(AV_BOOLNAME) || name.equals(AV_INTNAME);
    }

    private static Pair<Integer, Integer> getArgumentRange(String name) {
        int i = 0;
        int j = 0;

        for (int k = 0; k < name.length(); k++) {
            if (name.charAt(k) == '<') {
                i = k;
            }
            if (name.charAt(k) == '>') {
                j = k;
            }
        }

        return new Pair<Integer, Integer>(i + 1, j);
    }

    private static List<String> getTypeArguments(String name) {

        Pair<Integer, Integer> range = getArgumentRange(name);
        if (range.fst > range.snd) // no type arguments
            return new ArrayList<>();
        return Arrays.asList(name.substring(range.fst, range.snd).split(","));
    }
    
    public static String replaceLast(String string, String toReplace, String replacement) {
        int pos = string.lastIndexOf(toReplace);
        if (pos > -1) {
            return string.substring(0, pos)
                 + replacement
                 + string.substring(pos + toReplace.length(), string.length());
        } else {
            return string;
        }
    }
    
    
    private static String normalizeSort(String name) {
        
        List<String> sorts = Arrays.asList(name.split("<"));
        
        StringBuilder sb = new StringBuilder();
        for (String s : sorts) {
            sb.append("<");
            sb.append(s.substring(0, 1).toUpperCase());
            sb.append(s.substring(1));
        }
        
        return sb.toString().replaceFirst("<", "");
        
    }
    
    private static String addTypeArguments(String name, List<String> arguments) {
        
        StringBuilder sb = new StringBuilder(name);
        sb.append("<");
        for (String a : arguments) {
            sb.append(normalizeSort(a));
            sb.append(",");
        }
        sb.append(">");
       // System.out.println("RE " + replaceLast(sb.toString(),",",""));
        return replaceLast(sb.toString(),",","");
        
    }
    public static String opToSMT(FunctionSymbol fs) {

        String name = fs.getName();
       // System.out.println("FS " + fs.toString());
       // System.out.println(getTypeArguments(name));
        List<String> typeArgs = getTypeArguments(name);       
        boolean hasTypeArguments = !typeArgs.isEmpty();
        
        Operation op = hasTypeArguments ? OperationMatcher.matchOp(name.split("<")[0]):OperationMatcher.matchOp(name);
  
           
        if (!op.isPoly()) {

           // System.out.println("RE " + op.toSMT());
            return op.toSMT();
        }
        return addTypeArguments(op.toSMT(), typeArgs);

    }

    
    
    public static boolean isBoolean(String str) {
        return (str.toLowerCase().equals("true") || str.toLowerCase().equals("false"));
    }

    public static boolean isNumeric(String str) {
        DecimalFormatSymbols currentLocaleSymbols = DecimalFormatSymbols.getInstance();
        char localeMinusSign = currentLocaleSymbols.getMinusSign();

        if (!Character.isDigit(str.charAt(0)) && str.charAt(0) != localeMinusSign)
            return false;

        boolean isDecimalSeparatorFound = false;
        char localeDecimalSeparator = currentLocaleSymbols.getDecimalSeparator();

        for (char c : str.substring(1).toCharArray()) {
            if (!Character.isDigit(c)) {
                if (c == localeDecimalSeparator && !isDecimalSeparatorFound) {
                    isDecimalSeparatorFound = true;
                    continue;
                }
                return false;
            }
        }
        return true;
    }

    public static SymbolTable getSymbolTable() {
        return symbolTable;
    }

    
    
    public static void addSymbol(FunctionSymbol fs) {
        String name = fs.getName();
        System.out.println("NAME " + fs.getName());
        Operation op = null;

        if (isNumeric(name) || isBoolean(name))
            return;

//        if (name.startsWith("$")) {
//
//            op = getOp(name);
//
//            if (specialOps.contains(op) || op.equals(Operation.ANON)) {
//
//            } else {
//                if (!op.isPoly())
//                    return;
//            }
//
//        }

//        if (!isFunc(name) && !specialOps.contains(op)) {
//            nfs = new FunctionSymbol(Names.makeSMTName(name), fs.getResultSort(), fs.getArgumentSorts());
//        } else if (specialOps.contains(op)) {
//            nfs = new FunctionSymbol(Names.makeSMTName(name.substring(1)), fs.getResultSort(), fs.getArgumentSorts());
//        } else {
//            nfs = new FunctionSymbol(name, fs.getResultSort(), fs.getArgumentSorts());
//        }
        
        //FunctionSymbol nfs;
        if (!symbolTable.getAllSymbols().contains(fs)) {

            symbolTable = symbolTable.addFunctionSymbol(fs);
             System.out.println("OK");

        }
    }

    
    //============================================================//
    
    
    
    
    public static String parseFuncSignature(String name) {

        if (name.indexOf('<') == -1)
            return "";

        name = name.substring(name.indexOf("<") + 1);

        return parsePolyString(name.trim());
    }

    public static String parsePolyString(String name) {

        String typed = CharMatcher.anyOf(">").removeFrom(name);
        Iterable<String> types = Splitter.on("<").split(typed);
        List<String> sorts = Arrays.asList(Iterables.toArray(types, String.class));

        String r = "";

        for (String so : sorts) {
            if (so.contains(",")) {
                String[] parts = so.split(",");
                for (String p : parts) {
                    r += nmap.computeIfAbsent(p, x -> p.substring(0, 1).toUpperCase() + p.substring(1));
                    r += ".";
                }
                r = r.substring(0, r.length() - 1);
                return r;
            }

            r += nmap.computeIfAbsent(so, x -> so.substring(0, 1).toUpperCase() + so.substring(1));
        }
        return r;
    }

    public static String normalizeSort(Sort s) {
        String name = s.toString();

        if (smap.containsKey(name)) {
            // System.out.println("N " + name);
            return smap.get(name);
        }

        // if (!name.contains("<")) {
        // for (String t : smap.keySet()) {
        // name = name.replaceAll("(?i)"+t, smap.get(t));
        // }
        // }
        String r = parsePolyString(name);
        // if(r.equals("ArrayInt"))
        // return "ArrInt";
        // //return parsePolyString(name);
        return r;
    }

    
    public static Set<Dependency> getDependencies() {
        Set<Dependency> deps = new LinkedHashSet<>();
        for (FunctionSymbol fs : symbolTable.getAllSymbols()) {
            // System.out.println("Entry: " + fs.getName());
            if (fs.getName().startsWith("$")) {
                Dependency d = new FuncDependency(fs);
                deps.add(d);
            } else {
                Dependency d = new ConstDependency(fs);
                deps.add(d);
            }
        } // debug
          // for (Dependency d : deps) {
          // System.out.println("d:" + d.instantiate().toString());
          // }
        return deps;
    }

   
    public static Operation getOp(String name) {

        Iterable<String> operators = Splitter.on("<").split(name);

        List<String> ops = Arrays.asList(Iterables.toArray(operators, String.class));

        Operation op = OperationMatcher.matchOp(ops.get(0));
        return op;
    }

    public static List<String> getSubTypes(FunctionSymbol type) {
        List<String> types = new ArrayList<>();
        for (Sort s : type.getArgumentSorts()) {
            if (s.getArguments().size() == 0) {
                types.add(normalizeSort(s));
            } else {
                String ty = "";
                for (Sort t : s.getArguments()) {
                    ty += normalizeSort(t);
                }
                types.add(ty);
            }

        }
        return types;
    }

    public static List<String> getSubTypes(Sort sort) {

        String typed = CharMatcher.anyOf(">").removeFrom(sort.toString());
        Iterable<String> types = Splitter.on("<").split(typed);
        List<String> subsorts = Arrays.asList(Iterables.toArray(types, String.class)).stream()
                .map(so -> nmap.computeIfAbsent(so, x -> so.substring(0, 1).toUpperCase() + so.substring(1)))
                .collect(Collectors.toList());

        return subsorts;
    }

    public static List<List<String>> getSubTypes(List<Sort> argumentSorts) {
        List<List<String>> sorts = new ArrayList<>();
        for (Sort sort : argumentSorts) {

            sorts.add(getSubTypes(sort));

        }
        return sorts;
    }

    public static boolean isFunc(String name) {
        if (name.startsWith("$")) {

            for (String n : smap.keySet()) {
                if (name.startsWith(n)) {
                    return false;
                }
            }
            return true;
        }
        return false;
    }

    private static String normalizeName(String s) {
        String r = "";
        String[] parts = s.split(" ");
        if (parts.length == 1)
            return s.substring(0, 1).toUpperCase() + s.substring(1);
        for (String p : parts) {
            r += p.substring(0, 1).toUpperCase() + p.substring(1);
        }

        return r;

    }

    public static List<String> getFuncArguments(FunctionSymbol type) {
        ArrayList<String> r = new ArrayList<>();

        String sign = type.toString().split("\\(")[0];
        int i = sign.indexOf("<");
        sign = sign.substring(i + 1);
        sign = CharMatcher.anyOf(">").replaceFrom(sign, " ");
        String[] parts = sign.split(",");
        for (String p : parts) {

            r.add(normalizeName(p.trim()));

        }
        // System.out.println("SIGN " + sign.substring(i+1));
        // String typed = CharMatcher.anyOf(">").removeFrom(type.toString());
        // Iterable<String> types = Splitter.on("<").split(typed);
        // List<String> subsorts = Arrays.asList(Iterables.toArray(types,
        // String.class));
        return r;
    }

    public static String addCasts(String smt) { // TODO better version

        List<String> sorts = new ArrayList<>();
        List<Pair<String, String>> consts = new ArrayList<>();
        List<String> critical = new ArrayList<>();
        Map<String, String> creplace = new HashMap<>();
        List<String> lines = Arrays.asList(smt.split("\\r?\\n"));
        Map<String, List<String>> casts = new HashMap<>();

        for (String l : lines) {

            if (l.trim().startsWith("(assert") && (l.contains("setInsertObject") || l.contains("inSetObject"))) {
                critical.add(l);
            }
            if (l.trim().startsWith("(declare-sort") && (!l.contains("Object"))) {
                sorts.add(l.split(" ")[1]);
            }
        }

        for (String sort : sorts) { // TODO axioms, declarations
            String c2o = "(" + sort + "2o";
            String o2c = "(o2" + sort;
            casts.put(sort, Arrays.asList(c2o, o2c));

            for (String l : lines) {

                if (l.trim().startsWith("(declare-const") && (l.contains(sort))) {
                    consts.add(new Pair<String, String>(l.split(" ")[1], l.split(" ")[2].replace(")", "")));

                }
            }
        }

        for (String c : critical) {
            String nc = c;

            for (Pair<String, String> p : consts) {

                String cr = casts.get(p.snd).get(0) + " " + p.fst + ")";
                nc = nc.replace(p.fst, cr);

            }
            creplace.put(c, nc);
        }

        String nsmt = "";

        int i;
        for (i = 0; i < lines.size(); i++) {
            if (lines.get(i).startsWith("(assert")) {
                break;
            }
            nsmt += lines.get(i) + "\r\n";

        }

        if (!critical.isEmpty() && !nsmt.contains("(declare-sort Object 0)"))
            nsmt += "(declare-sort Object 0) + \r\n";
        if (!critical.isEmpty()) {

            for (String t : sorts) {

                // declarations

                nsmt += "(declare-fun o2C (Object) C)".replace("C", t) + "\r\n";
                nsmt += "(declare-fun C2o (C) Object)".replace("C", t) + "\r\n";
                nsmt += "(declare-fun typeC (Object) Bool)".replace("C", t) + "\r\n";

                // axioms

                nsmt += "(assert (forall ((c C)) (! (= (o2C (C2o c)) c) :pattern ((o2C (C2o c))))))".replace("C", t)
                        + "\r\n";
                nsmt += "(assert (forall ((c C)) (! (typeC (C2o c)) :pattern ((o2C (C2o c))))))".replace("C", t)
                        + "\r\n";
                nsmt += "(assert (forall ((o Object)) (=>(typeC o) (= (C2o (o2C o)) o))))".replace("C", t) + "\r\n";

            }
        }
        // insert axioms,decl

        for (; i < lines.size(); i++) {

            String line = lines.get(i);

            if (critical.contains(line)) {
                nsmt += creplace.get(line) + "\r\n";
            } else {
                nsmt += line + "\r\n";
            }
        }
        return nsmt;

    }

}