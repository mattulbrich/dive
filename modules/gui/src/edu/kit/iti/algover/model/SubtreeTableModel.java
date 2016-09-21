package edu.kit.iti.algover.model;

import javax.swing.table.AbstractTableModel;
import javax.swing.table.DefaultTableModel;

/**
 * Created by sarah on 9/19/16.
 */
public class SubtreeTableModel extends AbstractTableModel {
    ProjectTree tree;

    public SubtreeTableModel(ProjectTree t){
        this.tree = t;

    }

    @Override
    public int getRowCount() {
        if(tree != null){
            if(tree instanceof CustomLeaf){
                CustomLeaf leaf = (CustomLeaf) tree;
                return leaf.rowCount;
            }
            else {

                return tree.rowCount;
            }
        }
        return 0;
    }

    @Override
    public int getColumnCount() {
        if(tree != null){
            if(tree instanceof CustomLeaf){
                CustomLeaf leaf = (CustomLeaf) tree;
                return leaf.colCount;
            }
            else {

                return tree.colCount;
            }
        }
        return 0;
    }

    @Override
    public Object getValueAt(int rowIndex, int columnIndex) {
        if(tree != null){

            if(tree instanceof CustomLeaf){
                CustomLeaf leaf = (CustomLeaf) tree;
                return leaf.getDetails()[rowIndex][columnIndex];
            }
            else {

                return tree.getDetails()[rowIndex][columnIndex];
            }
        }
        return null;

    }
}
