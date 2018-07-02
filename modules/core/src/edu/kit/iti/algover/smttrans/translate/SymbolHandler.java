package edu.kit.iti.algover.smttrans.translate;

import java.util.ArrayList;
import java.util.List;
import edu.kit.iti.algover.smttrans.data.Operation;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;

public class SymbolHandler {
    
    
    
    
    
    public static List<Dependency> handleOperation(Operation op) {
        
        switch (op) {
        case HEAP:  
            return handleHeap(op);

        default:
            break;
        }
        
        return new ArrayList<>();
    }
    
    
    private static List<Dependency> handleHeap(Operation op) {
        List<Dependency> r = new ArrayList<>();
        ConstDependency d = new ConstDependency(new FunctionSymbol(op.toSMT(), Sort.HEAP));
        r.add(d);
        return r;
        
        
        
        
    }
    

}
