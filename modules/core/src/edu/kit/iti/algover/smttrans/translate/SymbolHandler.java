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
       // r.add(f2);
        return r;

    }
    

    public static void handleFunc(String name) {
        
        Operation.FUNC.setSMT(name.replace("$$", ""));
    }
    
    

    
}
