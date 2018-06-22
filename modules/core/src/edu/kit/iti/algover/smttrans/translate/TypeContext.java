package edu.kit.iti.algover.smttrans.translate;
//

import java.text.DecimalFormatSymbols;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
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

public class TypeContext {
    private static SymbolTable symbolTable = new MapSymbolTable(new HashSet<FunctionSymbol>());
    public static final String AV_ARRNAME = "array";
    public static final String SMT_ARRNAME = "Arr";
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

        nmap.put(AV_ARRNAME, SMT_ARRNAME);
        nmap.put(AV_ARR2NAME, SMT_ARR2NAME);
        nmap.put(AV_INTNAME, SMT_INTNAME);
        nmap.put(AV_BOOLNAME, SMT_BOOLNAME);
        nmap.put(AV_HEAPNAME, SMT_HEAPNAME);
        nmap.put(AV_AHEAP, Operation.AHEAP.toSMT());
        nmap.put(AV_DECR, Operation.DECR.toSMT());
        // nmap.put(AV_HEAPNAME, Operation.HEAP.toSMT());
        // nmap.put(AV_ANON, Operation.ANON.toSMT());
        // nmap.put(AV_EVERYTHINGNAME, Operation.EVERYTHING.toSMT());
        nmap.put(AV_AHEAP, Operation.AHEAP.toSMT());

    }

    public static BiMap<String, String> getDefaults() {

        return nmap;
    }

    // public static boolean isBuiltInVar(String name) {
    // String n = name.substring(1);
    // return n.equals(AV_HEAPNAME) || n.equals(AV_MODNAME) ||
    // n.equals(AV_EVERYTHINGNAME);
    // }

    public static boolean isBuiltIn(Sort s) {
        String name = s.getName().toLowerCase();
        return name.equals(AV_BOOLNAME) || name.equals(AV_INTNAME);
    }

    public static String opToSMT(FunctionSymbol fs) {
        // System.out.println("Poly " + poly);
        String poly = fs.getName();
        String typed = CharMatcher.anyOf(">").removeFrom(poly);
        Iterable<String> operators = Splitter.on("<").split(typed);
        List<String> ops = Arrays.asList(Iterables.toArray(operators, String.class));

        // System.out.println("FS " + ops.get(0));

        Operation op = OperationMatcher.matchOp(ops.get(0));
        String sname = op.toSMT();
        // sname += nmap.computeIfAbsent(s, x -> s.substring(0, 1).toUpperCase() +
        // s.substring(1));
        if (op.isPoly()) {

            for (String s : ops.subList(1, ops.size())) {

                if (s.contains(",")) {

                    String[] parts = s.split(",");
                    for (String p : parts) {
                        sname += nmap.computeIfAbsent(p, x -> p.substring(0, 1).toUpperCase() + p.substring(1));
                        sname += ".";
                    }
                    sname = sname.substring(0, sname.length() - 1);
                    return sname;
                }

            }

            for (String s : ops.subList(1, ops.size())) {
                sname += nmap.computeIfAbsent(s, x -> s.substring(0, 1).toUpperCase() + s.substring(1));

            }

        }
        return sname;

    }

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
           
        
//        if (!name.contains("<")) {
//            for (String t : smap.keySet()) {
//                name = name.replaceAll("(?i)"+t, smap.get(t));
//            }
//        }
        String r = parsePolyString(name);
//        if(r.equals("ArrayInt"))
//            return "ArrInt";
//        //return parsePolyString(name);
        return r;
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

    public static void addSymbol(FunctionSymbol fs) {
        String name = fs.getName();
        Operation op = null;

        if (isNumeric(name) || isBoolean(name))
            return;

        if (name.startsWith("$")) {

            op = getOp(name);

            if (specialOps.contains(op) || op.equals(Operation.ANON)) { // TODO

            } else {
                if (!op.isPoly())
                    return;
            }

        }
        FunctionSymbol nfs;
        if (!isFunc(name) && !specialOps.contains(op)) {
            nfs = new FunctionSymbol(Names.makeSMTName(name), fs.getResultSort(), fs.getArgumentSorts());
        } else if (specialOps.contains(op)) {
            nfs = new FunctionSymbol(Names.makeSMTName(name.substring(1)), fs.getResultSort(), fs.getArgumentSorts());
        } else {
            nfs = new FunctionSymbol(name, fs.getResultSort(), fs.getArgumentSorts());
        }
        if (!symbolTable.getAllSymbols().contains(nfs)) {

            symbolTable = symbolTable.addFunctionSymbol(nfs);
            // System.out.println(symbolTable.getAllSymbols().toString());

        }
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

        return s;

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

}
