/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */
package edu.kit.iti.algover.swing.actions.io;

import edu.kit.iti.algover.swing.DiveCenter;
import edu.kit.iti.algover.swing.Main;
import edu.kit.iti.algover.swing.actions.BarAction;
import edu.kit.iti.algover.swing.actions.BarManager.Initialisable;
import edu.kit.iti.algover.swing.util.ExceptionDialog;

import java.awt.event.ActionEvent;
import java.io.File;

/**
 * This allows for reloading of the problem. If no problem was loaded yet, the
 * last attempt to load a file will be repeated.
 *
 * @author timm.felden@felden.com
 */

public class MostRecentProblemAction extends BarAction implements Initialisable {

    private static final long serialVersionUID = 8652614246864976171L;

    @Override
    public void initialised() {
        DiveCenter proofCenter = getDiveCenter();
        if (proofCenter != null) {
            proofCenter.properties().onGoingProof.addObserver(ongoing -> setEnabled(!ongoing));
        }
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        String recent = RecentProblemsMenu.getMostRecentProblem();

        if (recent == null) {
            ExceptionDialog.showExceptionDialog(getParentFrame(), "There is no recent problem to reload.");
            return;
        }

        try {
            Main.openDiveCenter(new File(recent));
        } catch (Exception ex) {
            ExceptionDialog.showExceptionDialog(getParentFrame(), ex);
        }
    }
}
