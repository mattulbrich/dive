package edu.kit.iti.algover.smttrans.translate;

import java.util.List;

import edu.kit.iti.algover.smttrans.data.Axiom;

public abstract class Dependency {

    protected Type t;

    public Dependency(Type t) {
        this.t = t;
    }
    
    public abstract List<Axiom> instantiate();

}
