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
    public static final String AV_HEAPNAME = "$heap";
    public static final String SMT_HEAPNAME = "Heap";
    public static final String AV_MODNAME = "$mod";
    public static final String AV_ANON = "$anon";
    public static final String AV_EVERYTHINGNAME = "$everything";
    public static final String AV_AHEAP = "$aheap";
    public static final String AV_DECR = "$decr";

    private static Set<Dependency> preamble = new LinkedHashSet<>();

    // private static BiMap<String, String> nmap = HashBiMap.create();

    // static {

    // nmap.put(AV_MODNAME, Operation.MOD.toSMT());
    // nmap.put(AV_SETEMPTYNAME, SMT_SETEMPTYNAME);
    // nmap.put(AV_ARRNAME, SMT_ARRNAME);
    // nmap.put(AV_ARR2NAME, SMT_ARR2NAME);
    // nmap.put(AV_INTNAME, SMT_INTNAME);
    // nmap.put(AV_BOOLNAME, SMT_BOOLNAME);
    // nmap.put(AV_HEAPNAME, SMT_HEAPNAME);
    // nmap.put(AV_AHEAP, Operation.AHEAP.toSMT());
    // nmap.put(AV_DECR, Operation.DECR.toSMT());
    //
    // }

    public static boolean isBuiltIn(String s) {
        String name = s.toLowerCase();
        return name.equals(AV_BOOLNAME) || name.equals(AV_INTNAME) || name.equals(AV_HEAPNAME);
    }

    // public static BiMap<String, String> getDefaults() {
    // return nmap;
    // }

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

    public static List<String> getTypeArguments(String name) {

        Pair<Integer, Integer> range = getArgumentRange(name);
        if (range.fst > range.snd) // no type arguments
            return new ArrayList<>();

        List<String> r = new ArrayList<>();
        Arrays.asList(name.substring(range.fst, range.snd).split(",")).forEach(x -> r.add(normalizeSort(x)));
        return r;
    }

    public static String replaceLast(String string, String toReplace, String replacement) {
        int pos = string.lastIndexOf(toReplace);
        if (pos > -1) {
            return string.substring(0, pos) + replacement + string.substring(pos + toReplace.length(), string.length());
        } else {
            return string;
        }
    }

    public static String normalizeSort(String name, String sorts) {
        // String r = addTypeArguments(normalizeSort(fs.getResultSort().getName()),
        // getTypeArguments(fs.toString()));
        String r = addTypeArguments(normalizeSort(name), getTypeArguments(sorts));

        return r.replace("<>", "");
    }

    public static String normalizeSort(String name) {

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
            sb.append(".");
        }
        sb.append(">");
        return replaceLast(sb.toString(), ".", "");

    }

    public static String opToSMT(FunctionSymbol fs) {

        String name = fs.getName();
        ;
        List<String> typeArgs = getTypeArguments(name);
        boolean hasTypeArguments = !typeArgs.isEmpty();

        Operation op = hasTypeArguments ? OperationMatcher.matchOp(name.split("<")[0]) : OperationMatcher.matchOp(name);

        if (!op.isPoly()) {

            return op.toSMT();
        }
        return addTypeArguments(op.toSMT(), typeArgs);

    }

    public static Operation getOperation(String name) {
        List<String> typeArgs = getTypeArguments(name);
        boolean hasTypeArguments = !typeArgs.isEmpty();
        Operation op = hasTypeArguments ? OperationMatcher.matchOp(name.split("<")[0]) : OperationMatcher.matchOp(name);
        return op;

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

    private static boolean isBuiltInType(String name) {

        if (isNumeric(name) || isBoolean(name))
            return true;

        return false;
    }

    private static boolean isRelevant(FunctionSymbol fs) {
        String name = fs.getName();

        Operation op = null;
        if (isBuiltInType(name))
            return false;

        if (isFunc(name)) {
            op = getOperation(name);

            if (op.isBuiltIn()) {
                return false;
            }
        }

        return true;
    }

    public static void addSymbol(FunctionSymbol fs) {
        if (!isRelevant(fs))
            return;

        if (isFunc(fs.getName()) && getOperation(fs.getName()).isSpecial()) {

            preamble.addAll(SymbolHandler.handleOperation(getOperation(fs.getName())));

        } else if (!symbolTable.getAllSymbols().contains(fs)) {
            symbolTable = symbolTable.addFunctionSymbol(fs);

        }
    }

    public static String getNullSort(String s) { // TODO deal with null
        return "X";
    }

    public static boolean isFunc(String name) {
        return name.startsWith("$");
    }

    public static Set<Dependency> getDependencies() {
        Set<Dependency> deps = new LinkedHashSet<>();
        deps.addAll(preamble);
        preamble.clear(); // cleanup

        for (FunctionSymbol fs : symbolTable.getAllSymbols()) {
            if (isFunc(fs.getName())) {
                Dependency d = new FuncDependency(fs);
                deps.add(d);
            } else {
                Dependency d = new ConstDependency(fs);
                deps.add(d);
            }
        }
        return deps;
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