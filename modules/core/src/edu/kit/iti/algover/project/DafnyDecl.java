package edu.kit.iti.algover.project;

import edu.kit.iti.algover.parser.DafnyTree;

import java.io.File;

/**
 * Created by sarah on 8/4/16.
 */
public class DafnyDecl {

    /**
     * Reference to ASTs that represents this DafnyDecl
     */
    private DafnyTree representation;
    /**
     * File, in which this DafnyDecl is stored in
     */
    private File file;

    private String name;

    public DafnyDecl(File file, DafnyTree tree, String name){
        this.representation = tree;
        this.file = file;
        this.name = name;
    }

    public DafnyDecl(){


    }
}
