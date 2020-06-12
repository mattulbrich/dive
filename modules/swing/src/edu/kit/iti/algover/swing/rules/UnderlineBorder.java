/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *  
 */

package edu.kit.iti.algover.swing.rules;

import javax.swing.border.Border;
import java.awt.*;

public class UnderlineBorder implements Border {
    private Color color;
    private int thickness;

    public UnderlineBorder(Color color, int thickness) {
        this.color = color;
        this.thickness = thickness;
    }

    @Override
    public void paintBorder(Component c, Graphics g, int x, int y, int width, int height) {
        g.setColor(color);
        for (int i = 1; i <= thickness; i++) {
            g.drawLine(x, y + height - i, x + width, y + height - i);
        }
    }

    @Override
    public Insets getBorderInsets(Component c) {
        return new Insets(0,0, thickness, 0);
    }

    @Override
    public boolean isBorderOpaque() {
        return true;
    }
}
