/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.dafnystructures;

import edu.kit.iti.algover.parser.DafnyTree;

/**
 * A DafnyField is a field in a DafnyClass
 * It is global and has a type and a name
 */
public class DafnyField extends DafnyDecl {

    private DafnyTree type;

    public DafnyTree getType() {
        return type;
    }

    public DafnyField(String filename, DafnyTree representation,
            DafnyTree type, String name, boolean inLibrary) {
        super(filename, representation, name, inLibrary);
        this.type = type;

    }

    public DafnyField(String filename, boolean inLibrary, DafnyTree child) {
        this(filename, child, child.getChild(1), child.getChild(0).getText(), inLibrary);
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
