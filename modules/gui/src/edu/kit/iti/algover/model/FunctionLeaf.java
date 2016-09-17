package edu.kit.iti.algover.model;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.dafnystructures.DafnyFunction;

import javax.swing.tree.TreeNode;
import java.util.Enumeration;

/**
 * Created by sarah on 9/15/16.
 */
public class FunctionLeaf extends CustomLeaf{

    DafnyFunction function;

    String status;

    public FunctionLeaf(DafnyFunction data, ProjectTree parent) {
        super(data, parent);
        this.function = data;
        //TODO
        this.status = "Test";

    }


    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public int getIndex(TreeNode node) {
        return 0;
    }

    @Override
    public Enumeration children() {
        return null;
    }

    public String getStatus(){
        return status;
    }


    public String getName() {
        return function.getName();
    }

    public String toString(){
        return this.function.getName();
    }

}
