/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.dafnystructures;

import edu.kit.iti.algover.parser.DafnyTree;

import java.io.File;

/**
 * A DafnyField is a field in a DafnyClass
 * It is global and has a type and a name
 */
public class DafnyField extends DafnyDecl {

    private DafnyTree type;

    // REVIEW: Why are these fields from DafnyDecl repeated in this class?
    // this seems to be very wrong.
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


    public DafnyField(File file, DafnyTree representation, DafnyTree type, String name){
        // REVIEW: Why is the representation the type ? ?
        this.representation = representation;
        this.name = name;
        this.type = type;
        this.file = file;

    }
    public String toString(){
    // REVIEW: Why is there a ";" at the end?
        return getType()+" "+getName()+";";
    }

    @Override
    public <R, A> R accept(DafnyDeclVisitor<R,A> visitor, A arg) {
        return visitor.visit(this, arg);
    }
}
