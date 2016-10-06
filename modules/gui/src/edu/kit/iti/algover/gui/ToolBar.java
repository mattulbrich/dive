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

    public JTextField getProjPath() {
        return projPath;
    }

    public void setProjPath(JTextField projPath) {
        this.projPath = projPath;
    }

    public JButton getButtonZ3() {
        return buttonZ3;
    }

    public void setButtonZ3(JButton buttonZ3) {
        this.buttonZ3 = buttonZ3;
    }

    public JButton getButtonDafny() {
        return buttonDafny;
    }

    public void setButtonDafny(JButton buttonDafny) {
        this.buttonDafny = buttonDafny;
    }

    public JButton getButtonKey() {
        return buttonKey;
    }

    public void setButtonKey(JButton buttonKey) {
        this.buttonKey = buttonKey;
    }

    JTextField projPath;
    JButton buttonZ3;
    JButton buttonDafny;
    JButton buttonKey;

    public ToolBar(GUICenter center)
    {
        projPath = new JTextField();
        buttonZ3 = new JButton(new ProveWithZ3Action(center));
        buttonDafny = new JButton(new ProveWithDafnyAction(center));
        buttonKey = new JButton(new ProveWithKeYAction(center));



        //buttonZ3.setActionCommand("z3");
        //buttonDafny.setActionCommand("dafny");
        //buttonKey.setActionCommand("key");

        //buttonZ3.addActionListener(new ButtonListener());
        //buttonDafny.addActionListener(new ButtonListener());
        //buttonKey.addActionListener(new ButtonListener());

        add(projPath);
        addSeparator();
        add(buttonZ3);
        add(buttonDafny);
        add(buttonKey);
    }
}
