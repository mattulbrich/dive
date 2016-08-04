package edu.kit.iti.algover.project;

import java.util.LinkedList;
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

    public String getName() {
        return name;
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

    /**
     * Functions belonging to this class, possibly empty
     */
    private List<DafnyFunction> functions;

    /**
     * Fields bleonging to this class, possibly empty
     */
    private List<DafnyField> fields;

    public DafnyClass(String name){
        this.name = name;
        this.methods = new LinkedList<>();
        this.functions = new LinkedList<>();
        this.fields = new LinkedList<>();

    }
}
