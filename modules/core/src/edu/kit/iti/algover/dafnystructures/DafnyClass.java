/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.dafnystructures;

import java.util.Collection;
import java.util.Map;

import edu.kit.iti.algover.parser.DafnyException;

/**
 * A class for a class in Dafny. It comprises mthods, functions and fields.
 */
public class DafnyClass extends DafnyDecl {

    /**
     * Methods belonging to this class, possibly empty
     */
    private final Map<String, DafnyMethod> methods;

    /**
     * Functions belonging to this class, possibly empty
     */
    private final Map<String, DafnyFunction> functions;

    /**
     * Fields belonging to this class, possibly empty
     */
    private final Map<String, DafnyField> fields;

    /**
     * Instantiates a new dafny class from data in a builder
     *
     * @param dcb the builder to take data from.
     * @throws DafnyException if names in methods/functions/fields clash.
     * @see DafnyClassBuilder
     */
    public DafnyClass(DafnyClassBuilder dcb) throws DafnyException {
        super(dcb.getFilename(), dcb.getRepresentation(), dcb.getName(), dcb.isInLibrary());
        this.methods = toMap(dcb.getMethods());
        this.functions = toMap(dcb.getFunctions());
        this.fields = toMap(dcb.getFields());

        checkNameConflict(dcb.getMethods(), dcb.getFunctions());

        setParentFor(methods.values());
        setParentFor(functions.values());
        setParentFor(fields.values());
    }

    /**
     * Gets an immutable view to all functions.
     *
     * @return the functions as an immutable collection.
     */
    public Collection<DafnyFunction> getFunctions() {
        return functions.values();
    }

    /**
     * Gets a function by name.
     *
     * @param name the name to look up.
     * @return the function, or <code>null</code> if not present.
     */
    public DafnyFunction getFunction(String name) {
        return functions.get(name);
    }

    /**
     * Gets an immutable view to all methods.
     *
     * @return the methods as an immutable collection.
     */
    public Collection<DafnyMethod> getMethods() {
        return methods.values();
    }

    /**
     * Gets a method by name.
     *
     * @param name the name to look up.
     * @return the method, or <code>null</code> if not present.
     */
    public DafnyMethod getMethod(String name) {
        return methods.get(name);
    }

    /**
     * Gets an immutable view to all fields.
     *
     * @return the fields as an immutable collection.
     */
    public Collection<DafnyField> getFields() {
        return fields.values();
    }

    /**
     * Gets a field by name.
     *
     * @param name the name to look up.
     * @return the field, or <code>null</code> if not present.
     */
    public DafnyField getField(String name) {
        return fields.get(name);
    }

    // REVIEW: toString() should be a oneliner.
    @Override
    public String toString() {
        // REVIEW refactor with new situation; use StringBuilder
        String classToString = "";

//        classToString += "Class "+this.getName() +"\nwith "+this.methods.size()+ " methods:\n";
//        if(this.methods != null) {
//            for (DafnyMethod method : this.getMethods()) {
//                classToString += method.toString() + "\n";
//
//            }
//        }
//        classToString += "with "+this.functions.size()+" functions:";
//        if(this.functions != null) {
//            for (DafnyFunction function : this.getFunctions()) {
//                classToString += function.toString() + "\n";
//            }
//        }
//
//        if(this.fields != null) {
//            classToString += "with " + this.fields.size() + " fields:";
//            for (DafnyField field : this.getFields()) {
//                classToString += field.toString() + "\n";
//            }
//        }
//        return classToString;

        return "class " + getName();
    }

    @Override
    public <R, A> R accept(DafnyDeclVisitor<R, A> visitor, A arg) {
        return visitor.visit(this, arg);
    }
}
