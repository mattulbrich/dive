package edu.kit.iti.algover.smttrans.translate;

import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;

public class FSFactory {
    
   // private static Sort current;//
    
    private static FunctionSymbol handleNull() {
       // FunctionSymbol fs = new FunctionSymbol("null"+"<"+current.toString()+">", current);
        FunctionSymbol fs = new FunctionSymbol("null",Sort.OBJECT);
        TypeContext.addSymbol(fs);
        return fs;
        
    }

    public static FunctionSymbol makeFS(String name, Sort sort) {
        FunctionSymbol nfs;
    
            if (name.toLowerCase().equals("null")) {
                return handleNull();
            }
                

        if (!TypeContext.isNumeric(name) && !(TypeContext.isBoolean(name))) {
            nfs = new FunctionSymbol(name.replace("_","."), sort);
        } else {
            nfs = new FunctionSymbol(name, sort);
        }
        TypeContext.addSymbol(nfs);
        return nfs;
    }

    public static FunctionSymbol makeFS(FunctionSymbol fs) {

        
//        if (fs.getName().startsWith("$")) {
//            
//
//            
//            String s = TypeContext.getNullSort(fs.getName());
//            if (s != null)
//                current = Sort.get(s);
//           
//        }
            FunctionSymbol nfs;
        String name = fs.getName();

        if (name.toLowerCase().equals("null")) {
            return handleNull();
        }

        if (!TypeContext.isNumeric(name) && !(TypeContext.isBoolean(name))&& !(TypeContext.isFunc(name))) {
            nfs = new FunctionSymbol(fs.getName().replace("_", ".").replace("$$", "."), fs.getResultSort(), fs.getArgumentSorts());
        } else {
            nfs = new FunctionSymbol(fs.getName(), fs.getResultSort(), fs.getArgumentSorts());
        }
        try {
            
        
        TypeContext.addSymbol(nfs);
        } catch (NullPointerException e) {
           System.err.println("NULL: " + fs.getName());
        }
        return nfs;
    }


}
