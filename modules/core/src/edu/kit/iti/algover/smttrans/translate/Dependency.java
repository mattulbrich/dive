package edu.kit.iti.algover.smttrans.translate;

import java.util.LinkedHashSet;
import edu.kit.iti.algover.term.FunctionSymbol;

public abstract class Dependency {

    protected FunctionSymbol fs;

    public Dependency(FunctionSymbol fs) {
        this.fs = fs;
    }


    public abstract LinkedHashSet<String> instantiate();
    public abstract LinkedHashSet<String> declare();


}
