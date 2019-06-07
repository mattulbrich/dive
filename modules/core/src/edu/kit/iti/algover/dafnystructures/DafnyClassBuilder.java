/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.dafnystructures;

import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * This is a mutable builder class for dafny classes. Collections are
 * initialized, other items are initially set to <code>null</code> and must be
 * assigned before cosntructing the class object.
 *
 * Use the {@link #build()} method to create the {@link DafnyClass} object.
 *
 * Call {@link #parseRepresentation(DafnyTree)} to read entries from an AST.
 * You may also add/set elements manually.
 *
 * @see DafnyClass
 *
 * @author Sarah Grebing
 * @author Mattias Ulbrich
 */
public class DafnyClassBuilder {

    /**
     * The filename to which the strucure belongs.
     */
    private String filename;

    /**
     * The class name.
     */
    private String name;

    /**
     * The collection of methods in the class to build.
     */
    private List<DafnyMethod> methods = new ArrayList<>();

    /**
     * The collection of functions in the class to build.
     */
    private List<DafnyFunction> functions = new ArrayList<>();

    /**
     * The collection of fields in the class to build.
     */
    private List<DafnyField> fields = new ArrayList<>();

    /**
     * The AST root point for this class.
     */
    private DafnyTree representation;

    /**
     * This flag is true iff the class is in a library file.
     */
    private boolean inLibrary;

    /**
     * Instantiates a new dafny class builder.
     */
    public DafnyClassBuilder() {
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    public List<DafnyMethod> getMethods() {
        return methods;
    }

    public List<DafnyFunction> getFunctions() {
        return functions;
    }

    public List<DafnyField> getFields() {
        return fields;
    }

    public String getFilename() {
        return filename;
    }

    public void setFilename(String filename) {
        this.filename = filename;
    }

    /**
     * Builds a DafnyClass from the data in this builder.
     *
     * @return the freshly ccreated dafny class
     * @throws DafnyException
     *             if data is missing or name clashes occur
     */
    public DafnyClass build() throws DafnyException {
        return new DafnyClass(this);
    }

    /**
     * Adds a field for the class.
     *
     * @param dafnyField the dafny field
     */
    public void addField(DafnyField dafnyField) {
        this.fields.add(dafnyField);
    }

    /**
     * Adds a function for the class.
     *
     * @param func the non-<code>null</code> function
     */
    public void addFunction(DafnyFunction func) {
        this.functions.add(Objects.requireNonNull(func));
    }

    /**
     * Adds a method for the class.
     *
     * @param meth the non-<code>null</code> method
     */
    public void addMethod(DafnyMethod meth) {
        this.methods.add(Objects.requireNonNull(meth));
    }

    public DafnyTree getRepresentation() {
        return representation;
    }

    /**
     * Set the representation for this class and parse the AST.
     *
     * @param representation the AST representation
     */
    public void parseRepresentation(DafnyTree representation) {

        assert this.representation == null
                : "A builder must not have its representation replaced";

        this.representation = representation;
        this.name = representation.getChild(0).toString();

        // todo iterate over all children
        for (int i = 1; i < representation.getChildCount(); i++) {
            DafnyTree child = representation.getChild(i);
            switch (child.getType()) {
            case DafnyParser.METHOD:
                DafnyMethodBuilder mb = new DafnyMethodBuilder();
                mb.setInLibrary(inLibrary);
                mb.setFilename(filename);
                mb.parseRepresentation(child);
                addMethod(mb.build());
                break;
            case DafnyParser.FUNCTION:
                DafnyFunctionBuilder fb = new DafnyFunctionBuilder();
                fb.setFilename(filename);
                fb.setInLibrary(inLibrary);
                fb.parseRepresentation(child);
                addFunction(fb.build());
                break;
            case DafnyParser.FIELD:
                addField(new DafnyField(filename, inLibrary, child));
                break;
            default:
                throw new Error("Unexpected type " + child.getType());
            }
        }
    }


    public boolean isInLibrary() {
        return inLibrary;
    }

    public void setInLibrary(boolean inLibrary) {
        this.inLibrary = inLibrary;
    }
}
