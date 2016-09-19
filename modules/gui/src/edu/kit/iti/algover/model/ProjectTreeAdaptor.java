package edu.kit.iti.algover.model;

import edu.kit.iti.algover.dafnystructures.*;
import edu.kit.iti.algover.project.Project;
import org.jdesktop.swingx.treetable.TreeTableModel;

import javax.swing.event.TreeModelListener;
import javax.swing.table.TableModel;
import javax.swing.tree.TreeModel;
import javax.swing.tree.TreePath;
import java.util.LinkedList;
import java.util.List;

/**
 * Created by sarah on 9/13/16.
 */
public class ProjectTreeAdaptor implements TreeTableModel {
    Project p;
    //List<DafnyDecl> projectstructure;

    public ProjectTreeAdaptor(Project project){
        this.p = project;

    }

    @Override
    public Object getRoot() {
        return p;
    }

    @Override
    public Object getChild(Object parent, int index) {
        if(parent instanceof Project){
           List<DafnyDecl> projectstructure = new LinkedList<>();
            projectstructure.addAll(((Project) parent).getClasses());
            projectstructure.addAll(((Project) parent).getMethods());
            projectstructure.addAll(((Project) parent).getFunctions());
            return projectstructure.get(index);
        }
        if(parent instanceof DafnyClass){
            List<DafnyDecl> classStructure = new LinkedList<>();
            classStructure.addAll(((DafnyClass) parent).getFields());
            classStructure.addAll(((DafnyClass) parent).getMethods());
            classStructure.addAll(((DafnyClass) parent).getFunctions());
            return classStructure.get(index);
        }


        return null;
    }

    @Override
    public int getChildCount(Object parent) {
        if(parent instanceof Project){
           List<DafnyDecl> projectstructure = new LinkedList<>();
            projectstructure.addAll(((Project) parent).getClasses());
            projectstructure.addAll(((Project) parent).getMethods());
            projectstructure.addAll(((Project) parent).getFunctions());
            return projectstructure.size();
        }
        if(parent instanceof DafnyClass){
            List<DafnyDecl> classStructure = new LinkedList<>();
            classStructure.addAll(((DafnyClass) parent).getFields());
            classStructure.addAll(((DafnyClass) parent).getMethods());
            classStructure.addAll(((DafnyClass) parent).getFunctions());
            return classStructure.size();
        }
            return 0;


    }

    @Override
    public boolean isLeaf(Object node) {
        if(node instanceof DafnyField){
            return true;
        }
        if(node instanceof DafnyMethod){
            return true;
        }
        if(node instanceof DafnyFunction){
            return true;
        }
        if(node instanceof DafnyClass){
            return false;
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

    @Override
    public Class<?> getColumnClass(int i) {
        if(i == 0){
            return p.getClass();
        }else{
            return this.getChild(p, i).getClass();

        }

    }

    @Override
    public int getColumnCount() {
        return 2;
    }

    @Override
    public String getColumnName(int i) {
        if(i == 0) {
            return "Object in Project";
        }else{
            return "Path";
        }
    }

    @Override
    public int getHierarchicalColumn() {
        return 0;
    }

    @Override
    public Object getValueAt(Object o, int i) {
        if(o instanceof DafnyClass && i == 0){
            return "Class "+ ((DafnyClass) o).getName();
        }if(o instanceof DafnyMethod && i == 0){
            return "Method "+ ((DafnyMethod) o).getName();
        }
        if(o instanceof DafnyFunction && i == 0){
            return "Function "+ ((DafnyFunction) o).getName();
        }
        if(o instanceof DafnyField && i == 0){
            return "Field "+ ((DafnyField) o).getName();
        }
        if(o instanceof DafnyClass && i == 1){
            return "Class";

        }if(o instanceof DafnyMethod && i == 1){
            return ((DafnyMethod) o).getParams();
        }
        if(o instanceof DafnyFunction && i == 0){
        return "Function "+ ((DafnyFunction) o).getParameters();
        }
        if(o instanceof DafnyField && i == 0){
        return "Field "+ ((DafnyField) o).getType();
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
