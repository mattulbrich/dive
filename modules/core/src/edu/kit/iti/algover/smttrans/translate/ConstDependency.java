package edu.kit.iti.algover.smttrans.translate;

import java.util.LinkedHashSet;

import edu.kit.iti.algover.smttrans.data.Axiom;
import edu.kit.iti.algover.smttrans.data.AxiomContainer;
import edu.kit.iti.algover.term.FunctionSymbol;

public class ConstDependency extends Dependency {

    private String name;

    public ConstDependency(FunctionSymbol fs) {
        super(fs);
        this.name = fs.getName();
    }

    @Override
    public LinkedHashSet<String> instantiate() {
        LinkedHashSet<String> inst = new LinkedHashSet<>();
        

        inst.addAll(AxiomContainer.instantiateSort(fs)); 

        StringBuilder sb = new StringBuilder();

        sb.append("(declare-const ");
        sb.append(name);
        sb.append(" ");
        sb.append(TypeContext.normalizeSort(fs.getResultSort()));
        sb.append(")");
        inst.add(sb.toString());
     //   System.out.println(inst);
        return inst;
    }
    
    @Override
    public LinkedHashSet<String> declare() {
        LinkedHashSet<String> inst = new LinkedHashSet<>();
            
        
        StringBuilder sb = new StringBuilder();
        inst.addAll(AxiomContainer.declareSort(fs));
        sb.append("(declare-const ");
        sb.append(name);
        sb.append(" :: ");
        sb.append(TypeContext.normalizeSort(fs.getResultSort()));
        sb.append(")");
        inst.add(sb.toString());
        return inst;
    }
    
    
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = super.hashCode();
        result = prime * result + ((name == null) ? 0 : name.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (!super.equals(obj))
            return false;
        if (!(obj instanceof ConstDependency))
            return false;
        ConstDependency other = (ConstDependency) obj;
        if (name == null) {
            if (other.name != null)
                return false;
        } else if (!name.equals(other.name))
            return false;
        return true;
    }

    @Override
    public String toString() {
        
        return this.name + " : " + this.fs.getName();
    }



}
