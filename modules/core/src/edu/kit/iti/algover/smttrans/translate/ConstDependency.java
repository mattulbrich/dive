package edu.kit.iti.algover.smttrans.translate;

import java.util.LinkedHashSet;

public class ConstDependency extends Dependency {

    private String name;

    public ConstDependency(String n, Type t) {
        super(t);
        this.name = n;
    }

    @Override
    public LinkedHashSet<String> instantiate() {
        LinkedHashSet<String> inst = new LinkedHashSet<>();
        
        //declare sort with type
        
        //declare-const
        StringBuilder sb = new StringBuilder();
        sb.append("(declare-const ");
        sb.append(name);
        sb.append(" ");
        sb.append(t.toString());
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
        
        return this.name + " : " + this.t.toString();
    }

}
