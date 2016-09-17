package edu.kit.iti.algover.model;

import edu.kit.iti.algover.dafnystructures.DafnyField;

import javax.swing.tree.TreeNode;
import java.util.Enumeration;

/**
 * Created by sarah on 9/15/16.
 */
public class FieldLeaf extends CustomLeaf {
    DafnyField field;

    String status;

    ProjectTree parent;

    public FieldLeaf(DafnyField f, ProjectTree p){
        super(f,p);
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
    public String toString() {
        return field.getName();
    }


}
