package edu.kit.iti.algover.model;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.dafnystructures.DafnyField;
import edu.kit.iti.algover.project.Project;

import javax.swing.tree.TreeNode;
import java.io.File;
import java.util.Enumeration;

/**
 * This class represents leaves of type DafnyField for the GUI model
 * Created by sarah on 9/15/16.
 */
public class FieldLeaf extends CustomLeaf {
    DafnyField field;

    String status;

    ProjectTree parent;

    public FieldLeaf(DafnyField f, ProjectTree p, Project pr){
        super(f,p, pr);
        this.field =f;
        this.parent =p;
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
        return "";
    }

    @Override
    public String getName() {
        return field.getName();
    }

    @Override
    public DafnyDecl getData() {
        return this.field;
    }

    @Override
    public String toString() {
        return field.getName();
    }

    @Override
    public String getFileName(){
        return parent.getFileName();
    }

    @Override
    public File getFile(){
        return parent.getFile();
    }
}
