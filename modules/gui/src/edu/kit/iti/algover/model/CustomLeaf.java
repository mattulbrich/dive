package edu.kit.iti.algover.model;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.project.Project;

import javax.swing.tree.TreeNode;
import java.util.Enumeration;

/**
 * Class represneting the leaves of the projecttree.
 * Created by sarah on 9/15/16.
 */
public abstract class CustomLeaf extends ProjectTree implements TreeNode {

    public DafnyDecl data;

    public ProjectTree parent;

    public Project p;







    public CustomLeaf(DafnyDecl data, ProjectTree parent, Project p){
        super(parent.name, p.getScript().getAbsolutePath());
        this.data = data;
        this.parent = parent;
        this.p = p;

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

    public abstract DafnyDecl getData();
    public abstract String toString();


}
