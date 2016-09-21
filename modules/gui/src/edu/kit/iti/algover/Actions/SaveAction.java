package edu.kit.iti.algover.Actions;

import edu.kit.iti.algover.gui.GUICenter;

import javax.swing.*;
import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;


/**
 * Created by Azadeh Shirvanian on 21.09.2016.
 */
public class SaveAction extends AbstractAction {

    GUICenter c;

    public SaveAction(GUICenter center){
        this.c = center;

        this.putValue(AbstractAction.NAME, "Save Project...");
        this.putValue(AbstractAction.ACCELERATOR_KEY, KeyStroke.getKeyStroke(KeyEvent.VK_S, KeyEvent.CTRL_MASK));
    }

    @Override
    public void actionPerformed(ActionEvent e) {

        System.out.println("Save Project");
    }
}
