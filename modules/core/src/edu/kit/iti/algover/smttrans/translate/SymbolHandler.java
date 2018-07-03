package edu.kit.iti.algover.smttrans.translate;

import java.util.ArrayList;
import java.util.List;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.smttrans.data.Operation;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;

public class SymbolHandler {

    public static List<Dependency> handleOperation(Operation op) {

        switch (op) {
        case HEAP:
            return handleHeap(op);

        case MOD:
            return handleMod(op);
        
        case EVERYTHING:
            return handleEverything(op);
            
//        case AHEAP:
//            return handleAheap(op);
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
    
//    private static List<Dependency> handleAheap(Operation op) {
//        List<Dependency> r = new ArrayList<>();
//        ConstDependency d = new ConstDependency(new FunctionSymbol(Names.makeSMTName(op.toSMT()), Sort.get("Heap")));
//        r.add(d);
//        return r;
//
//    }
    
    
}
