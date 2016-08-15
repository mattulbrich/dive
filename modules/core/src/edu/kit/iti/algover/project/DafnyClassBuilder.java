package edu.kit.iti.algover.project;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;

import java.util.LinkedList;
import java.util.List;

/**
 * Created by sarah on 8/5/16.
 */

public class DafnyClassBuilder {
    private String filename;
    private DafnyTree classTree;

    private String name;

    /**
     * Methods belonging to this class, possibly empty
     */
    private List<DafnyMethod> methods;

    public String getName() {
        return name;
    }


    /**
     * Functions belonging to this class, possibly empty
     */
    private List<DafnyFunction> functions;

    /**
     * Fields belonging to this class, possibly empty
     */
    private List<DafnyField> fields;

    public List<DafnyMethod> getMethods() {
        return methods;
    }

    public DafnyClassBuilder setName(String name) {
        this.name = name;
        System.out.println("Classbuilder set Name of class: " + this.name);
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

    public DafnyTree getTree() {
        return classTree;
    }

    /**
     * DafnyTree with class as root, needs to be traversed to call dafnydeclbuilder
     */
    private DafnyTree tree;

    public DafnyClassBuilder(String filename, DafnyTree tree) {
        this.functions = new LinkedList<>();
        this.methods = new LinkedList<>();
        this.fields = new LinkedList<>();
        this.filename = filename;
        this.classTree = tree;

    }

    public DafnyClassBuilder(DafnyTree dafnyClass) {
        this.tree = dafnyClass;
    }

    public DafnyClass buildClass() {
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
}
