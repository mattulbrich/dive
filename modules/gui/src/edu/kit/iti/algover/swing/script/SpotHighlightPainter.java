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
    private String string;

    public SpotHighlightPainter(Color color, String string) {
        this.color = color;
        this.string = string;
    }

    @Override
    public void paint(Graphics g, int p0, int p1, Shape bounds, JTextComponent c) {
        TextUI mapper = c.getUI();
        try {
            Rectangle r = mapper.modelToView(c, p0);
            Font font = c.getFont().deriveFont(Font.BOLD);
            g.setFont(font);
            g.setColor(color);
            g.drawString(string, r.x, r.y + g.getFontMetrics(font).getAscent());
            // g.fillOval(r.x, r.y + 3, 10, 10);
        } catch (BadLocationException e) {
            e.printStackTrace();
        }
    }
}
