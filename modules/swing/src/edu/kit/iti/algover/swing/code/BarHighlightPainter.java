/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.swing.code;

import org.fife.ui.rsyntaxtextarea.SquiggleUnderlineHighlightPainter;

import javax.swing.text.Highlighter.HighlightPainter;
import java.awt.*;

public class BarHighlightPainter extends SquiggleUnderlineHighlightPainter {
    private Color color;
    private int width;
    private double relativeHeight;

    public BarHighlightPainter(Color color, int width, double relativeHeight) {
        super(color);
        this.color = color;
        this.width = width;
        this.relativeHeight = relativeHeight;
    }

    @Override
    protected void paintSquiggle(Graphics g, Rectangle r) {
        g.setColor(color);
        int offset = (int) (r.height * relativeHeight - width/2d);

        g.fillRect(r.x, r.y + offset, r.width, width);
    }
}
