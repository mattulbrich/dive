package edu.kit.iti.algover.smttrans.translate;
//

import java.text.DecimalFormatSymbols;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

import com.google.common.base.Splitter;
import com.google.common.collect.Iterables;

import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.smttrans.data.Operation;
import edu.kit.iti.algover.smttrans.data.OperationMatcher;
import edu.kit.iti.algover.term.FunctionSymbol;

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


    public static String opToSMT(FunctionSymbol fs) { //TODO types, declarations -> Axiome
        //System.out.println("Poly " + poly);
        String poly = fs.getName();
        Iterable<String> operators = Splitter.on("<").split(poly);
      
      List<String> ops = Arrays.asList(Iterables.toArray(operators, String.class));
      
     // System.out.println("FS " + ops.get(0));
      
      
      Operation op = OperationMatcher.matchOp(ops.get(0));
      String sname = op.toSMT();
      
        

        return sname;


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
    public static void addSymbol(FunctionSymbol fs) { //TODO null,heap etc... Sorts (check argument sorts)
        String name = fs.getName();
        //System.out.println("POLYFS " + name);
        if(isNumeric(name) || isBoolean(name))
            return;
        
        if (name.startsWith("$")) {
            
          Iterable<String> operators = Splitter.on("<").split(name);
          
          List<String> ops = Arrays.asList(Iterables.toArray(operators, String.class));
          
          
          Operation op = OperationMatcher.matchOp(ops.get(0));
          if (!op.isPoly())
              return;
        }
  
        
        
        FunctionSymbol nfs = new FunctionSymbol(name, fs.getResultSort(), fs.getArgumentSorts());
        if (!symbolTable.getAllSymbols().contains(nfs))
            symbolTable = symbolTable.addFunctionSymbol(nfs);

    }

}
