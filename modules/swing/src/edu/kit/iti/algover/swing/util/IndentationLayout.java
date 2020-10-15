/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.swing.util;

import javax.swing.*;
import java.awt.*;

public class IndentationLayout implements LayoutManager {

    public static final String INDENTED_PROPERTY = "indented";
    private static final int GAP = 3;

    private final int indentation;

    public IndentationLayout(int indentation) {
        this.indentation = indentation;
    }

    public void addLayoutComponent(String name, Component comp) { }
    public void removeLayoutComponent(Component comp) { }

    public void layoutContainer(Container parent) {

        int width = parent.getWidth();
        Insets insets = parent.getInsets();

        int h = insets.top;
        for(int i = 0; i < parent.getComponentCount(); i++) {
            JComponent comp = (JComponent) parent.getComponent(i);
            Dimension prefd = comp.getPreferredSize();
            boolean indented = Boolean.TRUE.equals(comp.getClientProperty(INDENTED_PROPERTY));
            int leftOffset = insets.left + (indented ? indentation : 0);
            comp.setBounds(leftOffset, h,
                    width - leftOffset - insets.right, prefd.height);
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
        Dimension result = new Dimension(w + indentation + insets.left + insets.right,
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
        Dimension result = new Dimension(w + indentation + insets.left + insets.right,
                h-GAP + insets.top + insets.bottom);
        return result;
    }

}
