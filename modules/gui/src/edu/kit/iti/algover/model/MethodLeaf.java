package edu.kit.iti.algover.model;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.project.Project;

import javax.swing.tree.TreeNode;
import java.io.File;
import java.util.Enumeration;

/**
 * Class representing DafynMEthod leaves in projecttree
 * Created by sarah on 9/15/16.
 */
public class MethodLeaf extends CustomLeaf {
    DafnyMethod method;
    String status;
    ProjectTree parent;

    public MethodLeaf(DafnyMethod m, ProjectTree p, Project pr){
        super(m, p, pr);
        this.method = m;
        this.parent = p;
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

    @Override
    public String getStatus() {
        return status;
    }

    @Override
    public String getName() {
        return method.getMethodName();
    }

    @Override
    public DafnyDecl getData() {
        return this.method;
    }

    @Override
    public String toString() {
        return method.getMethodName();
    }
    @Override
    public String getFileName(){
        return this.method.getFilename();
    }

    @Override
    public File getFile(){
        return this.method.getFile();
    }

}
