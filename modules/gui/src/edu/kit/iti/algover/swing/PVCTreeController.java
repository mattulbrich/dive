/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.swing;

import edu.kit.iti.algover.project.Project;

import javax.swing.*;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.MutableTreeNode;
import javax.swing.tree.TreeNode;
import java.awt.*;
import java.util.Enumeration;

public class PVCTreeController {

    private final DiveCenter diveCenter;
    private final JScrollPane theComponent;
    private final JTree tree;

    public PVCTreeController(DiveCenter diveCenter) {
        this.diveCenter = diveCenter;
        tree = new JTree();
        theComponent = new JScrollPane(tree);

        diveCenter.project.addObserver(this::updateProject);
    }

    private void updateProject(Project project) {
        DefaultMutableTreeNode mtn = new DefaultMutableTreeNode("welt");
        mtn.add(new DefaultMutableTreeNode("hallo"));
        tree.setModel(new DefaultTreeModel(mtn));
    }

    public Component getComponent() {
        return theComponent;
    }
}
