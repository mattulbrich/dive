/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.model;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.project.Project;

import javax.swing.tree.TreeNode;
import java.io.File;
import java.util.Enumeration;

/**
 * Class represneting the leaves of the projecttree.
 * Created by sarah on 9/15/16.
 */
public abstract class CustomLeaf extends ProjectTree implements TreeNode {

    public DafnyDecl data;

    public ProjectTree parent;

    public Project p;

    public int rowCount;
    public int colCount;

    public int lineNumber;
    public CustomLeaf(DafnyDecl data, ProjectTree parent, Project p){
        super(parent.name, new File(data.getFilename()));
        this.data = data;
        this.parent = parent;
        this.p = p;
        this.colCount = 2;
        this.rowCount = 2;
        this.lineNumber = data.getRepresentation().getLine();

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
    @Override
    public Object[][] getDetails(){
        Object [][] details = new Object[2][2];
        details[0][0] = "Type";
        details[0][1] = this.name;
        details[1][0] = "Filename";
        details[1][1] = this.getData().getFilename();
        return details;
    }

    @Override
    public int getLineNumber(){
        return this.lineNumber;
    }
    @Override
    public abstract String getFileName();

    @Override
    public abstract File getFile();


}
