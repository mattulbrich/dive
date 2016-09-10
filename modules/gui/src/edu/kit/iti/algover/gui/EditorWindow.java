package edu.kit.iti.algover.gui;

import java.awt.*;
import javax.swing.*;

/**
 * EditorWindow with GridBagLayout consists of a menu bar, a toolbar, and
 * a panel (for the text area inside a tabbed pane).
 *
 * Created by sony on 06.09.2016.
 */

public class EditorWindow extends JFrame
{
    GridBagConstraints c = new GridBagConstraints();
    GridBagLayout gridbag = new GridBagLayout();

    public EditorWindow (MenuBar menuBar, ToolBar toolbar, EditorPanel panel) {

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
