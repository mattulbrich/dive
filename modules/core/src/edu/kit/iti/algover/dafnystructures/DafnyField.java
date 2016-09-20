package edu.kit.iti.algover.dafnystructures;

import edu.kit.iti.algover.parser.DafnyTree;

import java.io.File;

/**
 * A DafnyField is a field in a DafnyClass
 * It is global and has a type and a name
 */
public class DafnyField extends DafnyDecl {

    private DafnyTree type;
    private String name;

    @Override
    public DafnyTree getRepresentation() {
        return representation;
    }

    private DafnyTree representation;
    @Override
    public File getFile() {
        return file;
    }

    private File file;
    public DafnyTree getType() {
        return type;
    }


    public String getName() {
        return name;
    }


    public DafnyField(File file, DafnyTree type, String name){
        this.representation = type;
        this.name = name;
        this.type = type;
        this.file = file;

    }
    public String toString(){
        return getType()+" "+getName()+";";
    }
}
