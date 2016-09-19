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
            return tree.getDetails().length;
        }
        return 0;
    }

    @Override
    public int getColumnCount() {
        if(tree != null){
            return tree.getDetails().length;
        }
        return 0;
    }

    @Override
    public Object getValueAt(int rowIndex, int columnIndex) {
        if(tree != null){
            return tree.getDetails()[rowIndex][columnIndex];
        }
        return null;

    }
}
