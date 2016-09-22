package edu.kit.iti.algover.model;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;

import javax.swing.event.TreeModelListener;
import javax.swing.tree.TreeModel;
import javax.swing.tree.TreeNode;
import javax.swing.tree.TreePath;
import java.io.File;
import java.util.Enumeration;
import java.util.List;
import java.util.Objects;

/**
 * This class represents the projecttree structure for teh GUI model. It consists eiother of Projecttrees or of customleaves
 * Created by sarah on 9/15/16.
 */
public class ProjectTree implements TreeNode{



    public String name;
    public File path;
    public List<ProjectTree> children;
    public ProjectTree parent;
    public int rowCount;
    public int colCount;

    public DafnyDecl repr;

    public ProjectTree(String name, File path){
        this.setName(name);
        this.path = path;
        this.rowCount = 3;
        this.colCount = 2;

    }
    public void setChildren(List<ProjectTree> children) {
        this.children = children;
        this.rowCount += children.size();
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

    public Object[][] getDetails(){
        Object [][] details = new Object[rowCount][colCount];

        details[0][0] = "Type";
        details[0][1] = this.name;
        details[1][0] = "Path";
        details[1][1] = this.path;
        if(children.size() != 0) {
            details[2][0] = "Children";
            details[2][1] = this.getChildCount();
           int i = 3;
            for (ProjectTree child: this.children) {
                    if(child instanceof CustomLeaf) {
                        details[i][0] = ((CustomLeaf) child).getData().getRepresentation().getText();
                        details[i][1] = ((CustomLeaf) child).getData().getName();
                    }else{
                        details[i][0] = "Subtree";
                        details[i][1] = child.name;
                    }
                i++;
            }
        }
        return details;
    }

    public int getLineNumber(){
        return 0;
    }

    public String getFileName(){
        return this.path.getAbsoluteFile().getName();
    }

    public File getFile(){
        return this.path;
    }
}

