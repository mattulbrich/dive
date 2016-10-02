package edu.kit.iti.algover.gui;

import edu.kit.iti.algover.Actions.ProveWithDafnyAction;
import edu.kit.iti.algover.Actions.ProveWithKeYAction;
import edu.kit.iti.algover.Actions.ProveWithZ3Action;

import javax.swing.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

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

    public ToolBar(GUICenter center)
    {
        /*buttonZ3.setActionCommand("z3");
        buttonDafny.setActionCommand("dafny");
        buttonKey.setActionCommand("key");

        buttonZ3.addActionListener(new ButtonListener());
        buttonDafny.addActionListener(new ButtonListener());
        buttonKey.addActionListener(new ButtonListener());*/

        add(projPath);
        addSeparator();
        add(buttonZ3);
        add(buttonDafny);
        add(buttonKey);

        buttonZ3.setAction(new ProveWithZ3Action(center));
        buttonDafny.setAction(new ProveWithDafnyAction(center));
        buttonKey.setAction(new ProveWithKeYAction(center));
    }
}
