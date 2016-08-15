package edu.kit.iti.algover.project;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.term.Sort;

/**
 * A DafnyField is a field in a DafnyClass
 * It is global and has a type and a name
 */
public class DafnyField extends DafnyDecl {

    private DafnyTree type;
    private String name;

    public DafnyTree getType() {
        return type;
    }


    public String getName() {
        return name;
    }


    public DafnyField(DafnyTree type, String name){
        this.name = name;
        this.type = type;

    }
    public String toString(){
        return getType()+" "+getName()+";";
    }
}
