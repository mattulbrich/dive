package edu.kit.iti.algover.project;

import edu.kit.iti.algover.term.Sort;

/**
 * Created by sarah on 8/4/16.
 */
public class DafnyField extends DafnyDecl {

    private Sort type;
    private String name;
    private String value;

    public Sort getType() {
        return type;
    }

    public void setType(Sort type) {
        this.type = type;
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    public String getValue() {
        return value;
    }

    public void setValue(String value) {
        this.value = value;
    }

    public DafnyField(Sort type, String name, String value){
        this.setType(type);
        this.setName(name);
        this.setValue(value);

    }

    public String toString(){
        return getType().toString()+" "+getName()+ " := "+getValue()+";";
    }
}
