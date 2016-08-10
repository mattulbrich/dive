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

    /**
     * Functions belonging to this class, possibly empty
     */
    private List<DafnyFunction> functions;

    /**
     * Fields bleonging to this class, possibly empty
     */
    private List<DafnyField> fields;

    public DafnyClass(DafnyClassBuilder dcb){
        this.name = dcb.getName();
        this.methods = dcb.getMethods();
        this.functions = dcb.getFunctions();
        this.fields = dcb.getFields();

    }
}
