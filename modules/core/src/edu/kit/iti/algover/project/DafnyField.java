package edu.kit.iti.algover.project;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.term.Sort;

/**
 * A DafnyField is a field in a DafnyClass
 */
public class DafnyField extends DafnyDecl {

    private DafnyTree type;
    private String name;
    private DafnyTree value;

    public DafnyTree getType() {
        return type;
    }


    public String getName() {
        return name;
    }


    public DafnyTree getValue() {
        return value;
    }


    public DafnyField(DafnyTree dafnyField){
        //TODO get right Child
        this.type = dafnyField.getChild(1);
        this.name = dafnyField.getChild(0).getText();
       // this.value = dafnyField.getChild(1);

    }

    public String toString(){
        return getType()+" "+getName()+ " := "+getValue()+";";
    }
}
