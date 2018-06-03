package edu.kit.iti.algover.smttrans.translate;

import java.util.List;

import edu.kit.iti.algover.smttrans.data.Axiom;
import edu.kit.iti.algover.smttrans.data.Operation;

public class FuncDependency extends Dependency {

    private Operation op;

    public FuncDependency(Operation o, Type t) {
        super(t);
        this.op = o;
    }

    @Override
    public List<Axiom> instantiate() {
        // TODO Auto-generated method stub
        return null;
    }
    @Override
    public String toString() {
        return op.name() + " : " + this.t.toString();
    }

}
