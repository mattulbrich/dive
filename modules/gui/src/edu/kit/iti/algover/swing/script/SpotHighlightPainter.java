/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.swing.script;

import javax.swing.plaf.TextUI;
import javax.swing.text.BadLocationException;
import javax.swing.text.Highlighter.HighlightPainter;
import javax.swing.text.JTextComponent;
import java.awt.*;

public class SpotHighlightPainter implements HighlightPainter {

    private Color color;

    public SpotHighlightPainter(Color color) {
        this.color = color;
    }

    @Override
    public void paint(Graphics g, int p0, int p1, Shape bounds, JTextComponent c) {
        TextUI mapper = c.getUI();
        try {
            Rectangle r = mapper.modelToView(c, p0);
            g.setColor(color);
            g.fillOval(r.x, r.y + 3, 10, 10);
        } catch (BadLocationException e) {
            e.printStackTrace();
        }
    }
}
