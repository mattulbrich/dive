/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.swing.sequent;

import edu.kit.iti.algover.swing.util.Settings;

import javax.swing.*;
import javax.swing.border.AbstractBorder;
import javax.swing.border.Border;
import java.awt.*;

public class TagBorder implements Border {
    private static final Settings S = Settings.getInstance();
    private static final Font FONT = new Font("Sans serif", Font.PLAIN, 9);
    private static final Insets EMPTY_INSETS = new Insets(0,0,0,0);

    public static final String TAG_KEY = "proofFormulaLabels";

    @Override
    public void paintBorder(Component c, Graphics g, int x, int y, int width, int height) {
        JComponent cmp = (JComponent) c;
        Object labelProp = cmp.getClientProperty(TAG_KEY);
        if (labelProp == null || labelProp.toString().isEmpty()) {
            return;
        }
        String[] labels = labelProp.toString().split(",");
        int xpos = x + width;
        g.setClip(x, y, width, height);
        g.setFont(FONT);
        for (String label : labels) {
            label = label.trim();
            int tw = SwingUtilities.computeStringWidth(g.getFontMetrics(), label);
            Color color = S.getColor("dive.labelcolor." + label, Color.lightGray);
            g.setColor(color);
            g.fillRect(xpos - tw - 16, y, tw + 16, 13);
            g.setColor(Color.black);
            g.drawString(label, xpos - tw - 8, 11);
            xpos -= tw + 16;
        }
    }

    @Override
    public Insets getBorderInsets(Component c) {
        return EMPTY_INSETS;
    }

    @Override
    public boolean isBorderOpaque() {
        return false;
    }
}
