package edu.kit.iti.algover.gui;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

/**
 * Created by Azadeh Shirvanian on 14.09.2016.
 */
@Deprecated
public class ButtonListener implements ActionListener {

    public ButtonListener(){}

    public void actionPerformed(ActionEvent evt) {

        if (evt.getActionCommand().equals("z3"))
            System.out.println("Z3 button was clicked.");
        else if (evt.getActionCommand().equals("dafny"))
            System.out.println("Dafny button was clicked.");
        else if (evt.getActionCommand().equals("key"))
            System.out.println("KeY button was clicked.");

    }
}
