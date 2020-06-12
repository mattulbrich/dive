/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */
package edu.kit.iti.algover.swing.actions;

import java.awt.event.ActionEvent;
import java.awt.event.WindowEvent;
import java.awt.event.WindowListener;

import javax.swing.JOptionPane;

import edu.kit.iti.algover.swing.DiveCenter;
import edu.kit.iti.algover.swing.Main;
import edu.kit.iti.algover.swing.actions.BarManager.Initialisable;

/**
 * This GUI action is for closing a window.
 * 
 * Since there are both prover and editor windows, case
 * distinction have to be performed at couple of places.
 */
@SuppressWarnings("serial") 
public class CloseAction extends BarAction 
    implements Initialisable, WindowListener {

    public void initialised() {
        DiveCenter center = getDiveCenter();
        if(center != null)
            center.properties().onGoingProof.addObserver(ongoing -> setEnabled(!ongoing));
    }
    
    public void actionPerformed(ActionEvent e) {
        tryClose();
    }

    public void windowClosing(WindowEvent e) {
        if(isEnabled()) {
            tryClose();
        }
    }

    private void tryClose() {
        DiveCenter center = getDiveCenter();

        boolean changed = center.properties().unsavedChanges.getValue();

        if(changed) {
            int result = JOptionPane.showConfirmDialog(getParentFrame(),
                    "There are changes in the current window. Close anyway?",
                    "Close", JOptionPane.YES_NO_OPTION,
                    JOptionPane.WARNING_MESSAGE);
            
            if(result != JOptionPane.YES_OPTION)
                return;
        }
        
        Main.closeDiveCenter(center);
    }

    // WindowListener methods which are to be ignored
    
    public void windowDeactivated(WindowEvent e) {
    }

    public void windowDeiconified(WindowEvent e) {
    }

    public void windowIconified(WindowEvent e) {
    }

    public void windowOpened(WindowEvent e) {
    }

    public void windowActivated(WindowEvent e) {
    }

    public void windowClosed(WindowEvent e) {
    }

}
