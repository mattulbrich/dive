package edu.kit.iti.algover.smttrans.translate;

import java.util.List;

import edu.kit.iti.algover.smttrans.data.Axiom;

public class ConstDependency extends Dependency {

    private String name;

    public ConstDependency(String n, Type t) {
        super(t);
        this.name = n;
    }

    @Override
    public List<Axiom> instantiate() {
        // TODO Auto-generated method stub
        return null;
    }
    
    @Override
    public String toString() {
        
        return this.name + " : " + this.t.toString();
    }

}
