package edu.kit.iti.algover.project;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;

import java.util.LinkedList;
import java.util.List;

/**
 * Created by sarah on 8/5/16.
 */

public class DafnyClassBuilder {

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
 * Fields bleonging to this class, possibly empty
 */
private List<DafnyField> fields;

public List<DafnyMethod> getMethods() {
        return methods;
        }

    public DafnyClassBuilder setName(String name) {
        this.name = name;
        return this;
    }

    public DafnyClassBuilder setMethods(List<DafnyMethod> methods) {
        this.methods = methods;
        return this;
    }

    public DafnyClassBuilder setFunctions(List<DafnyFunction> functions) {
        this.functions = functions;
        return this;
    }

    public DafnyClassBuilder setFields(List<DafnyField> fields) {
        this.fields = fields;
        return this;
    }

    public List<DafnyFunction> getFunctions() {
        return functions;
        }

    public List<DafnyField> getFields() {
        return fields;
        }

    /**
     * DafnyTree with class as root, needs to be traversed to call dafnydeclbuilder
     */
    private DafnyTree tree;


    public DafnyClassBuilder(DafnyTree dafnyClass){
        this.tree = dafnyClass;
    }

    public DafnyClass buildClass(){
        //get class name from tree
        this.setName(this.tree.getChild(0).getText());

        List<DafnyTree> functions = tree.getChildrenWithType(DafnyParser.FUNCTION);
        LinkedList<DafnyFunction> tempFuncList = new LinkedList<>();
        for (DafnyTree function : functions) {
            DafnyFunction func = new DafnyFunction(function);
            tempFuncList.add(func);
        }
        this.setFunctions(tempFuncList);

        List<DafnyTree> methods = tree.getChildrenWithType(DafnyParser.METHOD);
        LinkedList<DafnyMethod> tempMethodList = new LinkedList<>();
        for (DafnyTree method : methods) {
            DafnyMethod meth = new DafnyMethod(method);
            tempMethodList.add(meth);
            //Create list, then add function
        }
        this.setMethods(tempMethodList);


        //traversetree and call dafnydeclbuilder


        return new DafnyClass(this);
    }
}
