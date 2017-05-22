/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.Actions;

import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.io.File;

import javax.swing.tree.TreePath;

import org.jdesktop.swingx.JXTreeTable;

import edu.kit.iti.algover.gui.GUICenter;
import edu.kit.iti.algover.model.CustomLeaf;
import edu.kit.iti.algover.model.ProjectTree;

/**
 * Created by sarah on 9/21/16.
 */
public class ProjectTreeMouseListener extends MouseAdapter {
    private final JXTreeTable treetable;
    private final GUICenter center;

    public ProjectTreeMouseListener(JXTreeTable treetable, GUICenter center) {
        this.treetable = treetable;
        this.center = center;
    }

    @Override
    public void mouseClicked(MouseEvent e) {

        if(e.getClickCount() == 1) {
            TreePath path = treetable.getPathForLocation(e.getX(), e.getY());
            ProjectTree lastPathComponent = (ProjectTree) path.getLastPathComponent();
            center.setSelectedPath(path);

            if(lastPathComponent.isLeaf()){
                CustomLeaf l = (CustomLeaf) lastPathComponent;
                File file = new File(/*perhaps take project fdir, */
                        l.getData().getFilename());
                center.setLoadedDafnySrc(file);
                center.setSelectedProjectSubTree(l);


            }else{
                center.setLoadedDafnySrc(lastPathComponent.path);
                center.setSelectedProjectSubTree(lastPathComponent);

            }
        }

        if(e.getClickCount() == 2) {
            TreePath path = treetable.getPathForLocation(e.getX(), e.getY());
            ProjectTree lastPathComponent = (ProjectTree) path.getLastPathComponent();
            center.setSelectedPath(path);
            if(lastPathComponent.isLeaf()){
                CustomLeaf l = (CustomLeaf) lastPathComponent;
                File file = new File(/*perhaps take project fdir, */
                        l.getData().getFilename());
                center.setLoadedDafnySrc(file);
                center.setSelectedLeaf(l);
            }else{
                center.setLoadedDafnySrc(lastPathComponent.path);
                center.setSelectedProjectSubTree(lastPathComponent);

            }
        }

    }
}