package edu.kit.iti.algover.smttrans.translate;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.smttrans.data.Operation;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.util.Pair;

public class SymbolHandler {

    public static List<Dependency> handleOperation(FunctionSymbol fs) {
        Operation op = TypeContext.getOperation(fs.getName()); 
        switch (op) {
        case HEAP:
            return handleHeap(op);

        case MOD:
            return handleMod(op);
        
        case EVERYTHING:
            return handleEverything(op);
            
        default:
            break;
        }

        return new ArrayList<>();
    }

    
    // implicit handling
    private static List<Dependency> handleMod(Operation op) {
        List<Dependency> r = new ArrayList<>();                                                
        ConstDependency d = new ConstDependency(new FunctionSymbol(Names.makeSMTName(op.toSMT()), Sort.get("Set<Object>")));
      
        r.add(d);
        return r;
    }

    private static List<Dependency> handleHeap(Operation op) {
        List<Dependency> r = new ArrayList<>();
        ConstDependency d = new ConstDependency(new FunctionSymbol(Names.makeSMTName(op.toSMT()), Sort.get("Heap")));
        r.add(d);
        return r;
    }
    
    private static List<Dependency> handleEverything(Operation op) {
        List<Dependency> r = new ArrayList<>();
        ConstDependency d = new ConstDependency(new FunctionSymbol(Names.makeSMTName(op.toSMT()), Sort.get("Set<Object>")));
        FuncDependency f = new FuncDependency(new FunctionSymbol("$everything<Object>", Sort.get("Object")));
      
        r.add(d);
        r.add(f);
        return r;

    }

//    private static List<Dependency> handleFunc(FunctionSymbol fs) {  //TODO
//        List<Dependency> r = new ArrayList<>();
////        ConstDependency d = new ConstDependency(new FunctionSymbol(Names.makeSMTName(op.toSMT()), Sort.get("Set<Object>")));
////        FuncDependency f = new FuncDependency(new FunctionSymbol("$everything<Object>", Sort.get("Object")));
////      
////        r.add(d);
////        r.add(f);
//        
//        System.out.println("FS " + fs.toString());
//        
//        String sign = fs.toString();
//        String name = sign.split("\\(")[0].trim().replace("$$", "");
//        String result = TypeContext.normalizeReturnSort(fs);
//        Pair<Integer, Integer> p = getArgumentRange(sign);
//        String args = sign.substring(p.fst, p.snd);
//        System.out.println("! " + name + " ! "+ args +" ! " + result);
//
//      FunctionSymbol nfs = new FunctionSymbol("$"+name, Sort.get(result), getArgs(sign));
//      FuncDependency f = new FuncDependency(nfs); 
//      
//      Operation.FUNC.setSMT(name);
//     //TypeContext.addSymbol(nfs);
//        //r.add(f);
//      SymbolTable t = TypeContext.getSymbolTable(); 
//      if (!t.getAllSymbols().contains(nfs)) {
//          TypeContext.setSymbolTable(t.addFunctionSymbol(nfs));
//      }
//      
//      
//         
//        r.add(f);
//        return r;
//
//    }
    
    
    

    public static void handleFunc(String name) {
        
        Operation.FUNC.setSMT(name.replace("$$", ""));
    }
    
    
    
//    private static List<Sort> getArgs(String sign) {
//        List<Sort> sorts = new ArrayList<>();
//        Pair<Integer, Integer> p = getArgumentRange(sign);
//        List<String> args = Arrays.asList(sign.substring(p.fst, p.snd).split(","));
//        for (String a : args) {
//            sorts.add(Sort.get(TypeContext.normalizeName(a.trim())));
//        }
//        
//        return sorts;
//        
//    }
//    private static Pair<Integer, Integer> getArgumentRange(String name) {
//        int i = 0;
//        int j = 0;
//
//        for (int k = 0; k < name.length(); k++) {
//            if (name.charAt(k) == '(') {
//                i = k;
//            }
//            if (name.charAt(k) == ')') {
//                j = k;
//            }
//        }
//
//        return new Pair<Integer, Integer>(i + 1, j);
//    }
//    private static List<Dependency> handleAheap(Operation op) {
//        List<Dependency> r = new ArrayList<>();
//        ConstDependency d = new ConstDependency(new FunctionSymbol(Names.makeSMTName(op.toSMT()), Sort.get("Heap")));
//        r.add(d);
//        return r;
//
//    }
    
    
}
