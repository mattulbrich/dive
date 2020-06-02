/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.swing.sequent;

import javax.swing.*;
import java.awt.*;

class SequentSeparator extends JComponent {

    private static final long serialVersionUID = -3610640407936158831L;

    public static int SEP_LENGTH = 32;
    public static int SEP_WIDTH = 6;

    public SequentSeparator() {
        setSize(SEP_LENGTH, SEP_LENGTH);
        setPreferredSize(getSize());
    }

    @Override
    public void paintComponent(Graphics g) {
        g.fillRect(0, 0, SEP_WIDTH, SEP_LENGTH);
        g.fillRect(0, (SEP_LENGTH - SEP_WIDTH) / 2, SEP_LENGTH, SEP_WIDTH);
    }
}