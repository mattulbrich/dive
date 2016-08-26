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
        super(dcb.getFilename(), dcb.getTree(), dcb.getName());
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
            classToString += classToString += "with " + this.fields.size() + " fields:";
            for (DafnyField field : this.fields) {
                classToString += field.toString() + "\n";
            }
        }
        return classToString;
    }
}
