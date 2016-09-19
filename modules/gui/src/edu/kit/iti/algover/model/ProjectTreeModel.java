package edu.kit.iti.algover.model;

import javax.swing.event.TreeModelListener;
import javax.swing.tree.TreeModel;
import javax.swing.tree.TreePath;

/**
 * Created by sarah on 9/16/16.
 */
public class ProjectTreeModel implements TreeModel {

    ProjectTree projectTree;

    public ProjectTreeModel(ProjectTree projectTree){
        this.projectTree = projectTree;
    }

    @Override
    public Object getRoot() {
        if(projectTree instanceof CustomLeaf){
            return projectTree.getParent();
        }else{
            return projectTree;
        }
    }

    @Override
    public Object getChild(Object parent, int index) {
        if(parent instanceof ProjectTree){
           ProjectTree p = (ProjectTree) parent;
            return p.getChildAt(index);
        }else{
            return null;
        }
    }



    @Override
    public int getChildCount(Object parent) {
        if(parent instanceof ProjectTree) {
            return ((ProjectTree) parent).getChildCount();
        }else{
            return 0;
        }
    }

    @Override
    public boolean isLeaf(Object node) {
        if(node instanceof ProjectTree) {
            return ((ProjectTree) node).isLeaf();
        }else{
            return false;
        }
    }

    @Override
    public void valueForPathChanged(TreePath path, Object newValue) {

    }

    @Override
    public int getIndexOfChild(Object parent, Object child) {
        return 0;
    }

    @Override
    public void addTreeModelListener(TreeModelListener l) {

    }

    @Override
    public void removeTreeModelListener(TreeModelListener l) {

    }


}
