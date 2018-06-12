package edu.kit.iti.algover.smttrans.translate;
//

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
import com.google.common.collect.Iterables;

import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.smttrans.data.Operation;
import edu.kit.iti.algover.smttrans.data.OperationMatcher;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;

public class TypeContext {
    private static SymbolTable symbolTable = new MapSymbolTable(new HashSet<FunctionSymbol>());
    public static final String AV_ARRNAME = "array"; // TODO more
    public static final String SMT_ARRNAME = "Arr";
    public static final String AV_INTNAME = "int";
    public static final String SMT_INTNAME = "Int";
    public static final String AV_BOOLNAME = "bool";
    public static final String SMT_BOOLNAME = "Bool";
    // public static final String AV_HEAPNAME = "heap";
    // public static final String SMT_HEAPNAME = "heap";
    private static Map<String, String> nmap = new HashMap<>();
    static {
        nmap.put(AV_ARRNAME, SMT_ARRNAME);
        nmap.put(AV_INTNAME, SMT_INTNAME);
        nmap.put(AV_BOOLNAME, SMT_BOOLNAME);

    }

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

        if (op.isPoly()) {
            for (String s : ops.subList(1, ops.size())) {
                sname += nmap.computeIfAbsent(s, x -> s.substring(0, 1).toUpperCase() + s.substring(1));
                ;
            }
        }
        return sname;

    }

    public static String normalizeSort(Sort s) {
        String name = s.toString();

        String typed = CharMatcher.anyOf(">").removeFrom(name);
        Iterable<String> types = Splitter.on("<").split(typed);
        List<String> sorts = Arrays.asList(Iterables.toArray(types, String.class));

        String r = "";
        for (String so : sorts) {
            r += nmap.computeIfAbsent(so, x -> so.substring(0, 1).toUpperCase() + so.substring(1));
        }
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

    public static void addSymbol(FunctionSymbol fs) { // TODO null,heap etc... Sorts (check argument sorts)
        String name = fs.getName();

        if (isNumeric(name) || isBoolean(name))
            return;

        if (name.startsWith("$")) {
            Operation op = getOp(name);

            if (!op.isPoly())
                return;
        }

        FunctionSymbol nfs = new FunctionSymbol(name, fs.getResultSort(), fs.getArgumentSorts());
        if (!symbolTable.getAllSymbols().contains(nfs))
            symbolTable = symbolTable.addFunctionSymbol(nfs);

    }

    public static Operation getOp(String name) {

        Iterable<String> operators = Splitter.on("<").split(name);

        List<String> ops = Arrays.asList(Iterables.toArray(operators, String.class));

        Operation op = OperationMatcher.matchOp(ops.get(0));
        return op;
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
        if (name.startsWith("$"))
            return true;
        return false;
    }

}
