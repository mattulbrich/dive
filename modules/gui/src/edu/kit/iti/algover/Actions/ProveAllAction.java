package edu.kit.iti.algover.Actions;

import edu.kit.iti.algover.gui.GUICenter;

import javax.swing.*;
import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;

/**
 * Created by Azadeh Shirvanian on 21.09.2016.
 */
public class ProveAllAction extends AbstractAction {

    GUICenter c;

    public ProveAllAction(GUICenter center){
        this.c = center;

        this.putValue(AbstractAction.NAME, "All Provers");
    }

    @Override
    public void actionPerformed(ActionEvent e) {

        System.out.println("Prove whole project with all provers.");
    }

}
