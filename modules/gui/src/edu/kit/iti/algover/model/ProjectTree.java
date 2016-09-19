package edu.kit.iti.algover.model;

import javax.swing.event.TreeModelListener;
import javax.swing.tree.TreeModel;
import javax.swing.tree.TreeNode;
import javax.swing.tree.TreePath;
import java.util.Enumeration;
import java.util.List;

/**
 * This class represents teh projecttree structure for teh GUI model. It consists eiother of Projecttrees or of customleaves
 * Created by sarah on 9/15/16.
 */
public class ProjectTree implements TreeNode{



    public String name;
    public String path;
    public List<ProjectTree> children;

    public ProjectTree parent;


    public ProjectTree(String name, String path){
        this.setName(name);
        this.path = path;
    }
    public void setChildren(List<ProjectTree> children) {
        this.children = children;
    }

    public void setParent(ProjectTree parent) {
        this.parent = parent;
    }

    public void setName(String name) {
        this.name = name;
    }
    @Override
    public TreeNode getChildAt(int childIndex) {
        return children.get(childIndex);
    }

    @Override
    public int getChildCount() {
        return children.size();
    }

    @Override
    public TreeNode getParent() {
        return this.parent;
    }

    @Override
    public int getIndex(TreeNode node) {
        return 0;
    }

    @Override
    public boolean getAllowsChildren() {
        return false;
    }

    @Override
    public boolean isLeaf() {
        return false;
    }

    @Override
    public Enumeration children() {
        return null;
    }

    public String toString(){
        String ret = this.name;

        return ret;

    }

}

