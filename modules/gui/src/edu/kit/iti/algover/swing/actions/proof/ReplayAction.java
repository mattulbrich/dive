/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.swing.actions.proof;

import edu.kit.iti.algover.swing.actions.BarAction;
import edu.kit.iti.algover.swing.actions.BarManager.InitialisingAction;

import javax.swing.*;
import java.awt.event.ActionEvent;
import java.util.concurrent.ExecutorService;

public class ReplayAction extends BarAction implements InitialisingAction  {

    public ReplayAction() {
        // initially not enaled.
        setEnabled(false);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        System.out.println("ReplayAction.actionPerformed");
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
        } finally {
            getDiveCenter().properties().onGoingProof.setValue(false);
            pm.setProgress(1);
            pm.close();
        }
    }
}
