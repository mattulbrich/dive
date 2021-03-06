/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */
package edu.kit.iti.algover.swing.actions;

import edu.kit.iti.algover.swing.DiveCenter;
import edu.kit.iti.algover.swing.Main;
import edu.kit.iti.algover.swing.actions.BarManager.Initialisable;

import java.awt.event.ActionEvent;

import javax.swing.JOptionPane;

@SuppressWarnings("serial")
public class ExitAction extends BarAction implements Initialisable {

    public ExitAction() {
        putValue(ACTION_COMMAND_KEY, "exit");
    }
    
    public void initialised() {
        DiveCenter center = getDiveCenter();
        if(center != null) {
            center.properties().onGoingProof.addObserver(ongoing -> setEnabled(!ongoing));
        }
    }

    public void actionPerformed(ActionEvent e) {

        boolean changed = Main.windowsHaveChanges();
        if(changed) {
            int result = JOptionPane.showConfirmDialog(getParentFrame(),
                    "There are changes in one open window. Exit anyway?",
                    "Exit", JOptionPane.YES_NO_OPTION,
                    JOptionPane.WARNING_MESSAGE);
            
            if(result != JOptionPane.YES_OPTION)
                return;
        }
        
        System.exit(0);
    }

}
