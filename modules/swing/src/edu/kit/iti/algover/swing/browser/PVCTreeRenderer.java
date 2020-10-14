/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.swing.browser;

import edu.kit.iti.algover.swing.DiveCenter;
import edu.kit.iti.algover.swing.browser.PVCBrowserController.TreeNode;
import edu.kit.iti.algover.swing.util.GUIUtil;

import javax.swing.*;
import javax.swing.tree.DefaultTreeCellRenderer;
import java.awt.*;

public class PVCTreeRenderer extends DefaultTreeCellRenderer {

    private static final Icon GREEN =
            GUIUtil.makeIcon(PVCTreeRenderer.class.getResource("img/green.png"));

    private static final Icon GREY =
            GUIUtil.makeIcon(PVCTreeRenderer.class.getResource("img/grey.png"));

    private static final Icon ORANGE =
            GUIUtil.makeIcon(PVCTreeRenderer.class.getResource("img/orange.png"));

    private final DiveCenter diveCenter;

    public PVCTreeRenderer(DiveCenter diveCenter) {
        this.diveCenter = diveCenter;
    }

    @Override
    public Component getTreeCellRendererComponent(JTree tree, Object value, boolean sel, boolean expanded, boolean leaf, int row, boolean hasFocus) {
        super.getTreeCellRendererComponent(tree, value, sel, expanded, leaf, row, hasFocus);
        if (value instanceof TreeNode) {
            TreeNode node = (TreeNode) value;
            String of;
            if (node.getCountAllPVC() >= 0) {
                of = String.format(" (%d/%d)", node.getCountFinishedPVCs(), node.getCountAllPVC());
            } else {
                of = "";
            }
            setText(String.format("<html><font color=\"blue\">%s</font>%s%s", node.getType(), node.getName(), of));

            switch (node.getStatus()) {
            case CLOSED:
                setIcon(GREEN);
                break;

            case OPEN:
            case FAILING:
                setIcon(ORANGE);
                break;

            default:
                setIcon(GREY);
            }

            setDisabledIcon(GREY);
        }

        return this;
    }


}
