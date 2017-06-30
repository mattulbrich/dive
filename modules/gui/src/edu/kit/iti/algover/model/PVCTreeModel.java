package edu.kit.iti.algover.model;

import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.PVCCollection;
import edu.kit.iti.algover.proof.PVCGroup;

import javax.swing.event.TreeModelListener;
import javax.swing.tree.TreeModel;
import javax.swing.tree.TreePath;

/**
 * Created by sarah on 10/21/16.
 */
public class PVCTreeModel implements TreeModel {

    private Project p;
    private ProjectTree t;


    public PVCTreeModel(Project p, ProjectTree t) {

        this.p = p;
        this.t = t;


    }

    @Override
    public Object getRoot() {
        return null;
    }

    @Override
    public Object getChild(Object parent, int index) {
        PVCGroup parentPVC = (PVCGroup)parent;

        return parentPVC.getChild(index);
    }

    @Override
    public int getChildCount(Object parent) {
        PVCGroup parentPVC = (PVCGroup)parent;
        return parentPVC.getChildren().size();
    }

    @Override
    public boolean isLeaf(Object node) {
        PVCCollection pvcC = (PVCCollection) node;
       return pvcC.isPVCLeaf();
    }

    @Override
    public void valueForPathChanged(TreePath path, Object newValue) {

    }

    @Override
    public int getIndexOfChild(Object parent, Object child) {
        if(parent instanceof PVCGroup){
            PVCGroup g = (PVCGroup) parent;
            if(g.getChildren().contains(child)){
                return g.getChildren().indexOf(child);

            }else{
                return 0;
            }
        }else{
            return 0;
        }

    }

    @Override
    public void addTreeModelListener(TreeModelListener l) {

    }

    @Override
    public void removeTreeModelListener(TreeModelListener l) {

    }
}
