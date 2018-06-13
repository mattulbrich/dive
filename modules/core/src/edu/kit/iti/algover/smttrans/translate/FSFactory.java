package edu.kit.iti.algover.smttrans.translate;

import java.text.DecimalFormatSymbols;

import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;

public class FSFactory {

    public static FunctionSymbol makeFS(String name, Sort sort) {
        FunctionSymbol nfs;

        if (!TypeContext.isNumeric(name) && !(TypeContext.isBoolean(name))) {
            nfs = new FunctionSymbol(name.replace("_","."), sort);
        } else {
            nfs = new FunctionSymbol(name, sort);
        }
        TypeContext.addSymbol(nfs);
        return nfs;
    }

    public static FunctionSymbol makeFS(FunctionSymbol fs) {

        FunctionSymbol nfs;
        String name = fs.getName();

        if (!TypeContext.isNumeric(name) && !(TypeContext.isBoolean(name))&& !(TypeContext.isFunc(name))) {
            nfs = new FunctionSymbol(fs.getName().replace("_", "."), fs.getResultSort(), fs.getArgumentSorts());
        } else {
            nfs = new FunctionSymbol(fs.getName(), fs.getResultSort(), fs.getArgumentSorts());
        }
        TypeContext.addSymbol(nfs);

        return nfs;
    }


}
