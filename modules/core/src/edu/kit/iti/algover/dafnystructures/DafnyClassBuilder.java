/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.dafnystructures;

import java.util.ArrayList;
import java.util.List;

import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;

/**
 * Created by sarah on 8/5/16.
 */

public class DafnyClassBuilder {

    private String filename;
    private String name;
    private List<DafnyMethod> methods = new ArrayList<>();
    private List<DafnyFunction> functions = new ArrayList<>();
    private List<DafnyField> fields = new ArrayList<>();
    private DafnyTree representation;
    private boolean inLibrary;

    public DafnyClassBuilder() {
    }

    public DafnyClassBuilder(String filename, DafnyTree tree) {
        setFilename(filename);
        parseRepresentation(tree);
    }

    public DafnyClassBuilder(String filename) {
        setFilename(filename);
    }

    /**
     * Methods belonging to this class, possibly empty
     */

    public String getName() {
        return name;
    }


    public List<DafnyMethod> getMethods() {
        return methods;
    }

    public DafnyClassBuilder setName(String name) {
        this.name = name;
     //   System.out.println("Classbuilder set Name of class: " + this.name);
        return this;
    }

/*
    public DafnyClassBuilder setMethods(List<DafnyMethod> methods) {
        this.methods = methods;
        System.out.println("Methods set");
        for (DafnyMethod m : methods) {
            System.out.println(m.toString());
        }
        return this;
    }

    public DafnyClassBuilder setFunctions(List<DafnyFunction> functions) {
        this.functions = functions;
        System.out.println("Functions set");
        for (DafnyFunction f : functions) {
            System.out.println(f.toString());
        }
        return this;
    }

    public DafnyClassBuilder setFields(List<DafnyField> fields) {
        this.fields = fields;
        System.out.println("Fields of class set: ");
        for (DafnyField f : this.fields) {
            System.out.println(f.toString());
        }
        return this;
    }

*/
    public List<DafnyFunction> getFunctions() {
        return functions;
    }

    public List<DafnyField> getFields() {
        return fields;
    }

    public String getFilename() {
        return filename;
    }

    private void setFilename(String filename) {
        this.filename = filename;
    }

    public DafnyClass build() throws DafnyException {
        return new DafnyClass(this);
    }

    public void addField(DafnyField dafnyField) {
        this.fields.add(dafnyField);
    }

    public void addFunction(DafnyFunction func) {
        this.functions.add(func);
    }

    public void addMethod(DafnyMethod meth) {
        this.methods.add(meth);
    }

    public DafnyTree getRepresentation() {
        return representation;
    }

    public void parseRepresentation(DafnyTree representation) {

        assert this.representation == null :
            "A builder must not have its representation replaced";

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
