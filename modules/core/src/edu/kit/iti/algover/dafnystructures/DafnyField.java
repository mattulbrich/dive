/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.dafnystructures;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;

/**
 * A DafnyField is a field in a DafnyClass. It is global and has a type and a
 * name.
 *
 * Since fields have less properties than methods or functions, there is no
 * builder for such entities.
 * @author Sarah Grebing
 * @author Mattias Ulbrich
 *
 */
// REVIEW. What does "global" mean here?

public class DafnyField extends DafnyDecl {

    /**
     * The AST which defines the type of the field.
     */
    private DafnyTree type;

    /**
     * Instantiates a new dafny field.
     *
     * @param filename the name of the file
     * @param representation the AST representation
     * @param type the type AST
     * @param name the field's name
     * @param inLibrary true if a field within a library
     */
    public DafnyField(String filename, DafnyTree representation,
            DafnyTree type, String name, boolean inLibrary) {
        super(filename, representation, name, inLibrary);
        this.type = type;

    }

    /**
     * Instantiates a new dafny field from an AST.
     *
     * @param filename the name of the containing file
     * @param inLibrary true if a field within a library
     * @param tree the AST from which the field is to be read
     */
    public DafnyField(String filename, boolean inLibrary, DafnyTree tree) {
        this(filename, tree,
                tree.getFirstChildWithType(DafnyParser.TYPE).getChild(0),
                tree.getChild(0).getText(), inLibrary);
    }


    /**
     * Gets the type of this field.
     *
     * @return the AST which contains the type definition.
     */
    public DafnyTree getType() {
        return type;
    }

    @Override
    public String toString() {
        // REVIEW: Why is there a ";" at the end?
        return getType() + " " + getName() + ";";
    }

    @Override
    public <R, A> R accept(DafnyDeclVisitor<R, A> visitor, A arg) {
        return visitor.visit(this, arg);
    }
}
