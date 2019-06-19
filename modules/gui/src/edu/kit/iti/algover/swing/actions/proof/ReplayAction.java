/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.swing.actions.proof;

import edu.kit.iti.algover.swing.actions.BarAction;
import edu.kit.iti.algover.swing.actions.BarManager.Initialisable;
import edu.kit.iti.algover.swing.util.Log;

import javax.swing.*;
import java.awt.event.ActionEvent;

public class ReplayAction extends BarAction implements Initialisable {

    public ReplayAction() {
        // initially not enaled.
        setEnabled(false);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        ProgressMonitor pm = new ProgressMonitor(getParentFrame(), "Replaying proof", "Note", 0, 1);
        getDiveCenter().getExecutor().submit(() -> replay(pm));
    }

    @Override
    public void initialised() {
        getDiveCenter().properties().activePVC.addObserver(pvc -> setEnabled(pvc != null));
    }

    private void replay(ProgressMonitor pm) {
        System.out.println("ReplayAction.replay");
        pm.setProgress(0);
        try {
            getDiveCenter().properties().onGoingProof.setValue(true);
            getDiveCenter().getMainController().getScriptCodeController().replay();
        } catch(Throwable ex) {
            Log.log(Log.DEBUG, "Uncaught exception in replay");
            Log.stacktrace(Log.DEBUG, ex);
        } finally {
            getDiveCenter().properties().onGoingProof.setValue(false);
            pm.setProgress(1);
            pm.close();
        }
    }
}
