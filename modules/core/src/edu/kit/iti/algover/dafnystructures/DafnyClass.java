/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.dafnystructures;

import java.util.Collection;
import java.util.Map;

import edu.kit.iti.algover.parser.DafnyException;

/**
 * Created by sarah on 8/4/16.
 */
public class DafnyClass extends DafnyDecl {

    /**
     * Methods belonging to this class, possibly empty
     */
    private Map<String, DafnyMethod> methods;

    /**
     * Functions belonging to this class, possibly empty
     */
    private Map<String, DafnyFunction> functions;

    /**
     * Fields belonging to this class, possibly empty
     */
    private Map<String, DafnyField> fields;

    public Collection<DafnyFunction> getFunctions() {
        return functions.values();
    }

    public Collection<DafnyMethod> getMethods() {
        return methods.values();
    }

    public Collection<DafnyField> getFields() {
        return fields.values();
    }

    public DafnyClass(DafnyClassBuilder dcb) throws DafnyException {
        super(dcb.getFilename(), dcb.getRepresentation(), dcb.getName(), dcb.isInLibrary());
        this.methods = toMap(dcb.getMethods());
        this.functions = toMap(dcb.getFunctions());
        this.fields = toMap(dcb.getFields());
    }

    public String toString(){
        String classToString = "";

        classToString += "Class "+this.getName() +"\nwith "+this.methods.size()+ " methods:\n";
        if(this.methods != null) {
            for (DafnyMethod method : this.getMethods()) {
                classToString += method.toString() + "\n";

            }
        }
        classToString += "with "+this.functions.size()+" functions:";
        if(this.functions != null) {
            for (DafnyFunction function : this.getFunctions()) {
                classToString += function.toString() + "\n";
            }
        }

        if(this.fields != null) {
            classToString += "with " + this.fields.size() + " fields:";
            for (DafnyField field : this.getFields()) {
                classToString += field.toString() + "\n";
            }
        }
        return classToString;
    }

    @Override
    public <R, A> R accept(DafnyDeclVisitor<R,A> visitor, A arg) {
        return visitor.visit(this, arg);
    }


    public DafnyField getField(String name) {
        return fields.get(name);
    }


    public DafnyMethod getMethod(String name) {
        return methods.get(name);
    }

    public DafnyFunction getFunction(String name) {
        return functions.get(name);
    }
}
