package edu.kit.iti.algover.project;

import edu.kit.iti.algover.parser.DafnyTree;

import java.io.File;

/**
 * Created by sarah on 8/4/16.
 */
public class DafnyDecl {

    public DafnyTree getRepresentation() {
        return representation;
    }

    public String getFilename() {
        return filename;
    }

    public String getName() {
        return name;
    }

    /**
     * Reference to ASTs that represents this DafnyDecl
     */
    private DafnyTree representation;
    /**
     * File, in which this DafnyDecl is stored in
     */
   // private File file;
    private String filename;

    private String name;

    public DafnyDecl(String filename, DafnyTree tree, String name){
        this.representation = tree;
        this.filename = filename;
        this.name = name;
    }

    public DafnyDecl(){


    }
}
