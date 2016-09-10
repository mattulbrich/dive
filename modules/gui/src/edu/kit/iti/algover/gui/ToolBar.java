package edu.kit.iti.algover.gui;

import javax.swing.*;

/**
 * ToolBar contains a text field and three buttons.
 * Buttons are separated from the text field.
 *
 * Created by sony on 07.09.2016.
 */

public class ToolBar extends JToolBar {

    JTextField projPath = new JTextField();
    JButton buttonZ3 = new JButton("Z3");
    JButton buttonDafny = new JButton("Dafny");
    JButton buttonKey = new JButton("KeY");

    public ToolBar()
    {
        add(projPath);
        addSeparator();
        add(buttonZ3);
        add(buttonDafny);
        add(buttonKey);
    }
}
