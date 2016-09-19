package edu.kit.iti.algover.model;

import org.jdesktop.swingx.treetable.TreeTableModel;

/**
 * Created by sarah on 9/19/16.
 */
public class ProjectTableTreeModel extends ProjectTreeModel implements TreeTableModel{

    ProjectTree t;
    public ProjectTableTreeModel(ProjectTree t){
        super(t);
        this.t = t;
    }

    @Override
    public Class<?> getColumnClass(int i) {
        return null;
    }

    @Override
    public int getColumnCount() {
        return 2;
    }

    @Override
    public String getColumnName(int i) {
        return null;
    }

    @Override
    public int getHierarchicalColumn() {
        return 0;
    }

    @Override
    public Object getValueAt(Object o, int i) {
        if(o instanceof CustomLeaf){
            if(i == 0){
                return ((CustomLeaf) o).name;
            }
            if(i == 1){
                return ((CustomLeaf) o).data;
            }
        }
        return null;
    }

    @Override
    public boolean isCellEditable(Object o, int i) {
        return false;
    }

    @Override
    public void setValueAt(Object o, Object o1, int i) {

    }
}
