package edu.kit.iti.algover.smttrans.translate;

import java.util.LinkedHashSet;

import edu.kit.iti.algover.smttrans.data.Axiom;
import edu.kit.iti.algover.smttrans.data.AxiomContainer;
import edu.kit.iti.algover.smttrans.data.Operation;
import edu.kit.iti.algover.term.FunctionSymbol;

public class FuncDependency extends Dependency {

    private Operation op;

    public FuncDependency(FunctionSymbol fs) {
        super(fs);
        this.op = TypeContext.getOperation(fs.getName());
    }

    @Override
    public LinkedHashSet<String> instantiate() {
        LinkedHashSet<String> inst = new LinkedHashSet<>();

        inst.addAll(AxiomContainer.instantiateSort(fs));
        for (Axiom a : op.getInstantiations()) {

            inst.addAll(AxiomContainer.instantiateAxiom(a, fs));
        }

        return inst;
    }

    @Override
    public String toString() {
        return op.name() + " : " + this.fs.getName();
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = super.hashCode();
        result = prime * result + ((op == null) ? 0 : op.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (!super.equals(obj))
            return false;
        if (!(obj instanceof FuncDependency))
            return false;
        FuncDependency other = (FuncDependency) obj;
        if (op != other.op)
            return false;
        return true;
    }

    @Override
    public LinkedHashSet<String> declare() {
        LinkedHashSet<String> inst = new LinkedHashSet<>();

        inst.addAll(AxiomContainer.declareSort(fs));
        for (Axiom a : op.getInstantiations()) {

            inst.add(AxiomContainer.declareAxiom(a, fs));
        }

        return inst;
    }

}
