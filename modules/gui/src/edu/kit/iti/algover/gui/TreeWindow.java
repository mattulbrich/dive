package edu.kit.iti.algover.gui;

import javax.swing.*;
import java.awt.*;

/**
 * Created by sony on 10.09.2016.
 */
@Deprecated
public class TreeWindow extends JFrame {

    GridBagConstraints c = new GridBagConstraints();
    GridBagLayout gridbag = new GridBagLayout();

    public TreeWindow (MenuBar menuBar, ToolBar toolbar, TreePanel panel) {

        setTitle("AlgoVer");
        setDefaultCloseOperation( JFrame.EXIT_ON_CLOSE );
        setBounds(250, 120, 300, 300);
        setLayout(gridbag);

        c.fill = GridBagConstraints.BOTH;
        c.weightx = 1;
        c.anchor = GridBagConstraints.FIRST_LINE_START;
        c.gridx = 0;
        c.gridy = 0;

        add(menuBar, c);

        c.gridy = 1;

        add(toolbar, c);

        c.gridy = 2;
        c.weightx = 0;
        c.weighty= 1;
        c.gridwidth = 3;
        c.gridheight = GridBagConstraints.REMAINDER;

        add(panel, c);
    }
}
