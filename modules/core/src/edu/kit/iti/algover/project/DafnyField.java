package edu.kit.iti.algover.project;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.term.Sort;

/**
 * A DafnyField is a field in a DafnyClass
 */
public class DafnyField extends DafnyDecl {

    private String type;
    private String name;
    private String value;

    public String getType() {
        return type;
    }

    public void setType(String type) {
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

    public DafnyField(DafnyTree dafnyField){
        //traverse Dafnytree to rertrieve field parts

    }

    public String toString(){
        return getType()+" "+getName()+ " := "+getValue()+";";
    }
}
