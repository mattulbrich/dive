/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.swing.sequent;

import java.awt.*;

class SequentLayoutManager implements LayoutManager {

    private static int GAP = 3;

    public void addLayoutComponent(String name, Component comp) { }
    public void removeLayoutComponent(Component comp) { }

    public void layoutContainer(Container parent) {

        int width = parent.getWidth();
        Insets insets = parent.getInsets();
        int leftMargin = SequentSeparator.SEP_LENGTH/2 + insets.left;

        int h = insets.top;
        for(int i = 0; i < parent.getComponentCount(); i++) {
            Component comp = parent.getComponent(i);
            Dimension prefd = comp.getPreferredSize();
            if(comp instanceof SequentSeparator) {
                comp.setLocation(insets.left, h);
            } else {
                comp.setBounds(leftMargin, h, width-leftMargin - insets.right, prefd.height);
            }
            h += prefd.height + GAP;
        }
    }

    public Dimension minimumLayoutSize(Container parent) {
        int w = 0;
        int h = 0;
        for(int i = 0; i < parent.getComponentCount(); i++) {
            Dimension prefd = parent.getComponent(i).getMinimumSize();
            w = Math.max(w, prefd.width);
            h += prefd.height + GAP;
        }
        Insets insets = parent.getInsets();
        Dimension result = new Dimension(w + SequentSeparator.SEP_LENGTH / 2 + insets.left + insets.right,
                h-GAP + insets.top + insets.bottom);
        return result;
    }

    public Dimension preferredLayoutSize(Container parent) {
        int w = 0;
        int h = 0;
        for(int i = 0; i < parent.getComponentCount(); i++) {
            Dimension prefd = parent.getComponent(i).getPreferredSize();
            w = Math.max(w, prefd.width);
            h += prefd.height + GAP;
        }
        Insets insets = parent.getInsets();
        Dimension result = new Dimension(w + SequentSeparator.SEP_LENGTH / 2 + insets.left + insets.right,
                h-GAP + insets.top + insets.bottom);
        return result;
    }

}
