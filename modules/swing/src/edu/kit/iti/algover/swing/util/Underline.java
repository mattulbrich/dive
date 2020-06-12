/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.swing.util;

import javax.swing.border.AbstractBorder;
import javax.swing.border.Border;
import java.awt.*;

public class Underline extends AbstractBorder {

    private Color color;

    public Underline(Color color) {
        this.color = color;
    }

    @Override
    public void paintBorder(Component c, Graphics g, int x, int y, int width, int height) {
        g.setColor(color);
        g.drawLine(0, c.getHeight()-2, c.getWidth(), c.getHeight()-2);
        g.drawLine(0, c.getHeight()-1, c.getWidth(), c.getHeight()-1);
    }
}
