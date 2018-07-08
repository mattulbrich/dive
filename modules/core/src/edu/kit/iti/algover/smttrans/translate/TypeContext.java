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
    public static final String AV_ARR2NAME = "array2";
    public static final String SMT_ARR2NAME = "Arr2";
    public static final String AV_INTNAME = "int";
    public static final String SMT_INTNAME = "Int";
    public static final String AV_BOOLNAME = "bool";
    public static final String SMT_BOOLNAME = "Bool";
    public static final String AV_HEAPNAME = "heap";
    public static final String SMT_HEAPNAME = "Heap";

    private static Set<Dependency> preamble = new LinkedHashSet<>();
    private static final Set<Operation> emptySorts = new LinkedHashSet<>(
            Arrays.asList(Operation.SETEMPTY, Operation.SEQEMPTY));
    private static final Set<Operation> builtinConsts = new LinkedHashSet<>(
            Arrays.asList(Operation.AHEAP, Operation.DECR));

    private static final Set<String> builtinTypes = new LinkedHashSet<>(
            Arrays.asList(AV_BOOLNAME, AV_INTNAME)); //, AV_HEAPNAME
    private static BiMap<String, String> nmap = HashBiMap.create();

    static {

        nmap.put(AV_ARRNAME, SMT_ARRNAME);
        nmap.put(AV_ARR2NAME, SMT_ARR2NAME);
        nmap.put(AV_INTNAME, SMT_INTNAME);
        nmap.put(AV_BOOLNAME, SMT_BOOLNAME);

    }

    
public static void reset() {
    preamble.clear();
    symbolTable = new MapSymbolTable(new HashSet<>());
}
    public static boolean isBuiltIn(String s) {
        return builtinTypes.contains(s.toLowerCase());
    }

    public static void setSymbolTable(SymbolTable symbolTable) {
        TypeContext.symbolTable = symbolTable;
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

    public static List<String> getTypeArguments(String name) {

        Pair<Integer, Integer> range = getArgumentRange(name);
        if (range.fst > range.snd) // no type arguments
            return new ArrayList<>();

        List<String> r = new ArrayList<>();
        Arrays.asList(name.substring(range.fst, range.snd).split(",")).forEach(x -> r.add(normalizeName(x)));
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
        String r = addTypeArguments(normalizeName(name), getTypeArguments(sorts));

        return r.replace("<>", "");
    }

    public static String normalizeReturnSort(FunctionSymbol fs) {

        // return normalizeName();
        // System.out.println("N " + fs.toString());
        String sign = fs.toString().split(":")[1].trim();
        String name = sign.split("<")[0].trim();
        return normalizeSort(name, sign);
    }

    public static String normalizeName(String name) {

        List<String> sorts = Arrays.asList(name.split("<"));

        StringBuilder sb = new StringBuilder();
        for (String s : sorts) {
            sb.append("<");
            sb.append(nmap.getOrDefault(s, s.substring(0, 1).toUpperCase() + s.substring(1)));
            // sb.append(s.substring(0, 1).toUpperCase());
            // sb.append(s.substring(1));
        }

        return cleanUp(sb.toString().replaceFirst("<", ""));

    }

    private static String cleanUp(String name) {

        int j = 0;
        int k = 0;

        for (int i = 0; i < name.length(); i++) {
            if (name.charAt(i) == '<') {
                j++;
            } else if (name.charAt(i) == '>') {
                k++;
            }
        }

        return name.substring(0, name.length() - (k - j));
    }

    private static String addTypeArguments(String name, List<String> arguments) {

        StringBuilder sb = new StringBuilder(name);
        sb.append("<");
        for (String a : arguments) {
            sb.append(normalizeName(a));
            sb.append(".");
        }
        sb.append(">");
        return replaceLast(sb.toString(), ".", "");

    }

    public static String opToSMT(FunctionSymbol fs) {

        String name = fs.getName();

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

    private static boolean isEmptySort(FunctionSymbol fs) {
        return (isFunc(fs.getName()) && emptySorts.contains(getOperation(fs.getName())));
    }

    private static Sort normalizeSort(Sort s) {
        // System.out.println("Sort " + s.toString());
        String sort = s.toString();
        List<String> parts = Arrays.asList(sort.replaceAll(">", "").split("<"));
        String name = parts.get(0);
        name = name.substring(0, 1).toUpperCase() + name.substring(1);
        // System.out.println(parts);
        sort = addTypeArguments(name, parts.subList(1, parts.size()));

        return Sort.get(sort);
    }

    private static FunctionSymbol makeEmptySort(Operation op, FunctionSymbol fs) {

        String sname = addTypeArguments(op.toSMT(), getTypeArguments(fs.getName()));
        String aname = fs.getName().substring(1, fs.getName().length());

        FunctionSymbol nfs = new FunctionSymbol(Names.makeSMTName(aname, sname), normalizeSort(fs.getResultSort()));
        preamble.add(new FuncDependency(fs));
        return nfs;

    }

    private static FunctionSymbol handleEmptySort(FunctionSymbol fs) {
        Operation op = getOperation(fs.getName());
        return makeEmptySort(op, fs);
    }

    public static void addSymbol(FunctionSymbol fs) {
        if (!isRelevant(fs))
            return;

        if (isFunc(fs.getName()) && getOperation(fs.getName()).isSpecial()) {

            preamble.addAll(SymbolHandler.handleOperation(fs));

        } else {

            FunctionSymbol nfs = null;

            if (isEmptySort(fs)) {
                nfs = handleEmptySort(fs);

            } else {

                nfs = isFunc(fs.getName()) ? new FunctionSymbol(fs.getName(), fs.getResultSort(), fs.getArgumentSorts())
                        : new FunctionSymbol(Names.makeSMTName(fs.getName()), fs.getResultSort(),
                                fs.getArgumentSorts());

            }

            if (!symbolTable.getAllSymbols().contains(nfs)) {

                symbolTable = symbolTable.addFunctionSymbol(nfs);

            }
        }
    }

    public static String getNullSort(String s) {

        if (!s.startsWith("$eq"))
            return null;

        String sign = s.replace("$eq<", "").substring(0, s.length() - 5);

        String result = addTypeArguments(normalizeName(sign.split("<")[0]), getTypeArguments(sign)).replace("<>", "");

        return result;
    }

    public static boolean isFunc(String name) {

        for (Operation op : builtinConsts) {
            if (name.startsWith("$" + op.toSMT()))
                return false;
        }

        // if (name.startsWith("$aheap") || name.startsWith("$decr")) // special case ,
        // TODO
        // return false;

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

    private static Map<String, String> functions = new HashMap<>();
    private static String fibName = "fib";
    private static String fibDef = "; NOTE: temporary, hardcoded \r\n" + 
            "(declare-fun fib (Heap Int) Int)\r\n" + 
            "(assert (= (fib ~heap 0) 0))\r\n" + 
            "(assert (= (fib ~heap 1) 1))\r\n" + 
            "(assert (forall ((x Int)) (=> (> x 1) (= (fib ~heap x) (+ (fib ~heap (- x 1)) (fib ~heap (- x 2)))))))\r\n" + 
            "; "+"\r\n";
    static {
        

        functions.put(fibName, fibDef);

    }

    public static String addFunctions(String smt) { // TODO Temporary Implementation
        String nsmt = "";
        List<String> lines = Arrays.asList(smt.split("\\r?\\n"));
        int i;
        for (i = 0; i < lines.size(); i++) {
            if (lines.get(i).startsWith("(assert")) {
                break;
            }
            nsmt += lines.get(i) + "\r\n";

        }
        
        for (String f : functions.keySet()) {
            if (smt.contains(f))
                nsmt += functions.get(f); 
        }

        for (; i < lines.size(); i++) {

            String line = lines.get(i);

            nsmt += line + "\r\n";
        }

        return nsmt;
    }

    public static String addCasts(String smt) { // TODO better version

        List<String> sorts = new ArrayList<>();
        List<Pair<String, String>> consts = new ArrayList<>();
        List<String> critical = new ArrayList<>();
        Map<String, String> creplace = new HashMap<>();
        List<String> lines = Arrays.asList(smt.split("\\r?\\n"));
        Map<String, List<String>> casts = new HashMap<>();

        for (String l : lines) {

            if (l.trim().startsWith("(assert") && (l.contains("setInsert<Object>") || l.contains("inSet<Object>"))) {
                critical.add(l);
            }
            if (l.trim().startsWith("(declare-sort") && (!l.contains("Object"))) {
                sorts.add(l.split(" ")[1]);
            }
        }

        for (String sort : sorts) {
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

            for (String t : sorts) {

                for (String s : sorts) {

                    if (s.equals(t))
                        continue;
                    nsmt += "(assert (forall ((o Object )) (=> (typeC o) (not (typeV o)))))".replace("C", t)
                            .replace("V", s) + "\r\n";
                }
            }

        }

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