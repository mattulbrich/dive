//package edu.kit.iti.algover.smttrans.translate;
//
//import java.util.ArrayList;
//
//import java.util.Arrays;
//import java.util.List;
//
//import com.google.common.base.CharMatcher;
//import com.google.common.base.Splitter;
//import com.google.common.collect.Iterables;
//
//import edu.kit.iti.algover.data.SymbolTable;
//import edu.kit.iti.algover.smttrans.data.OperationMatcher;
//
//import edu.kit.iti.algover.smttrans.data.OperationType;
//import edu.kit.iti.algover.term.Sort;
//
//public class Type {
//
//    @Override
//    public int hashCode() {
//        final int prime = 31;
//        int result = 1;
//        result = prime * result + ((typeData == null) ? 0 : typeData.hashCode());
//        return result;
//    }
//
//    @Override
//    public boolean equals(Object obj) {
//        if (this == obj)
//            return true;
//        if (obj == null)
//            return false;
//        if (getClass() != obj.getClass())
//            return false;
//        Type other = (Type) obj;
//        if (typeData == null) {
//            if (other.typeData != null)
//                return false;
//        } else if (!typeData.equals(other.typeData))
//            return false;
//        return true;
//    }
//
//    private final String ARRNAME = "array";
//    private static SymbolTable table;
//    
//    public static void setTable(SymbolTable t) {
//        table = t;
//    }
//
//    public static Sort typeConst(String name) {
//       return table.getFunctionSymbol(name).getResultSort();
//    }
//    public final static Type makeBoolType() {
//        List<String> l = new ArrayList<>();
//        l.add("Bool");
//        return new Type(l);
//    }
//
//    public final static Type makeIntType() {
//        List<String> l = new ArrayList<>();
//        l.add("Int");
//        return new Type(l);
//    }
//
//    private List<String> typeData;
//
//    public Type() {
//        this.typeData = new ArrayList<>();
//    }
//
//    public Type(List<String> types) {
//
//        // try {
//        this.typeData = inferType(types);
//        // } catch (NullPointerException e) {
//        // System.out.println("NULL: ");
//        // System.out.println(types.toString());
//        // this.typeData = types;
//        // }
//
//    }
//
//    public Type(String name) {
//        List<String> t = new ArrayList<>();
//        t.add(name);
//        this.typeData = inferType(t);
//    }
//
//    public int getArity() {
//        return typeData.size();
//    }
//
//    public Type pop() {
//        List<String> l = typeData.subList(1, typeData.size());
//        return new Type(l);
//    }
//
//    public static Type typeOperation(String poly) {
//
//        String typedOp = CharMatcher.anyOf(">").removeFrom(poly);
//        Iterable<String> operators = Splitter.on("<").split(typedOp);
//        List<String> ops = Arrays.asList(Iterables.toArray(operators, String.class));
//        return new Type(ops);
//
//    }
//
//    public List<String> getTypeData() {
//        return typeData;
//    }
//
//    public static String getFS(String poly) {
//        String[] s = poly.split("<");
//        return s[0];
//    }
//
//    private List<String> inferType(List<String> data) {
//        List<String> type = new ArrayList<>();
//        for (String d : data) {
//            if (d.startsWith("$")) { // function
//                OperationType opt = OperationMatcher.matchOp(d).getType();
//                if (opt == OperationType.ANY)
//                    continue;
//                d = opt.getSMT();
//            }
//            if (d.toLowerCase().equals(ARRNAME))
//                d = OperationType.ARR.getSMT();
//            type.add(d);
//        }
//        return type;
//    }
//
//    @Override
//    public String toString() {
//        String ty = "";
//        for (String s : this.typeData) {
//            ty += s.substring(0, 1).toUpperCase() + s.substring(1);
//        }
//        return ty;
//    }
//
//}
