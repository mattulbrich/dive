/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.dafnystructures;

import java.util.List;

/**
 * Created by sarah on 8/4/16.
 */
public class DafnyClass extends DafnyDecl {

    /**
     * Name of the DafnyClass
     */
    private String name;

    /**
     * Methods belonging to this class, possibly empty
     */
    private List<DafnyMethod> methods;

    public List<DafnyFunction> getFunctions() {
        return functions;
    }


    public List<DafnyMethod> getMethods() {
        return methods;
    }

    public List<DafnyField> getFields() {
        return fields;
    }

    /**
     * Functions belonging to this class, possibly empty
     */
    private List<DafnyFunction> functions;

    /**
     * Fields belonging to this class, possibly empty
     */
    private List<DafnyField> fields;

    public DafnyClass(DafnyClassBuilder dcb){
        super(dcb.getFile(), dcb.getTree(), dcb.getName());
        this.name = dcb.getName();
        this.methods = dcb.getMethods();
        this.functions = dcb.getFunctions();
        this.fields = dcb.getFields();

    }

    public String toString(){
        String classToString = "";

        classToString += "Class "+this.name +"\nwith "+this.methods.size()+ " methods:\n";
        if(this.methods != null) {
            for (DafnyMethod method : this.methods) {
                classToString += method.toString() + "\n";

            }
        }
        classToString += "with "+this.functions.size()+" functions:";
        if(this.functions != null) {
            for (DafnyFunction function : this.functions) {
                classToString += function.toString() + "\n";
            }
        }

        if(this.fields != null) {
            classToString += "with " + this.fields.size() + " fields:";
            for (DafnyField field : this.fields) {
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
        // TODO Do this using maps (MU)
        for (DafnyField dafnyField : fields) {
            if(dafnyField.getName().equals(name)) {
                return dafnyField;
            }
        }
        return null;
    }


    public DafnyMethod getMethod(String name) {
        // TODO Do this using maps (MU)
        for (DafnyMethod dafnyMethod : methods) {
            if(dafnyMethod.getName().equals(name)) {
                return dafnyMethod;
            }
        }
        return null;
    }

    public DafnyFunction getFunction(String name) {
        // TODO Do this using maps (MU)
        for (DafnyFunction dafnyFunction : functions) {
            if(dafnyFunction.getName().equals(name)) {
                return dafnyFunction;
            }
        }
        return null;
    }
}
