package edu.kit.iti.algover.model;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.dafnystructures.DafnyFunction;
import edu.kit.iti.algover.project.Project;

import javax.swing.tree.TreeNode;
import java.io.File;
import java.util.Enumeration;

/**
 * this class represents leaves of type DafnyFucntion for the GUI model
 * Created by sarah on 9/15/16.
 */
public class FunctionLeaf extends CustomLeaf{

    DafnyFunction function;

    String status;

    public FunctionLeaf(DafnyFunction data, ProjectTree parent, Project p) {
        super(data, parent, p);
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

    @Override
    public DafnyDecl getData() {
        return this.function;
    }

    public String toString(){
        return this.function.getName();
    }
    @Override
    public String getFileName(){
        return this.function.getFilename();
    }

    @Override
    public File getFile(){
        return this.function.getFile();
    }

}
