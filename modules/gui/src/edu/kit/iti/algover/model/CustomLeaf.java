package edu.kit.iti.algover.model;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;

import javax.swing.tree.TreeNode;
import java.util.Enumeration;

/**
 * Created by sarah on 9/15/16.
 */
public abstract class CustomLeaf extends ProjectTree implements TreeNode {

    public DafnyDecl data;

    public ProjectTree parent;





    public CustomLeaf(DafnyDecl data, ProjectTree parent){
        super(parent.name);
        this.data = data;
        this.parent = parent;
    }
    @Override
    public TreeNode getChildAt(int childIndex) {
        return null;
    }

    @Override
    public abstract int getChildCount();

    @Override
    public TreeNode getParent() {
        return this.parent;
    }

    @Override
    public abstract int getIndex(TreeNode node);

    @Override
    public boolean getAllowsChildren() {
        return false;
    }

    @Override
    public boolean isLeaf() {
        return true;
    }

    @Override
    public abstract Enumeration children();

    public abstract String getStatus();

    public abstract String getName();
//    public String toString(){
//        return this.data.getName();
//    }

    public abstract String toString();


}
