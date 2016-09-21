package edu.kit.iti.algover.Actions;

import edu.kit.iti.algover.gui.GUICenter;

import javax.swing.*;
import java.awt.event.ActionEvent;

/**
 * Created by Azadeh Shirvanian on 21.09.2016.
 */
public class ProveWithKeYAction extends AbstractAction {

    GUICenter c;

    public ProveWithKeYAction(GUICenter center){
        this.c = center;

        this.putValue(AbstractAction.NAME, "KeY");
    }

    @Override
    public void actionPerformed(ActionEvent e) {

        System.out.println("Prove whole project with KeY.");
    }
}
