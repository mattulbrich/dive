/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.swing.actions.io;

import edu.kit.iti.algover.swing.actions.BarAction;
import edu.kit.iti.algover.swing.actions.BarManager.Initialisable;
import edu.kit.iti.algover.swing.util.ExceptionDialog;

import java.awt.event.ActionEvent;
import java.io.IOException;
import java.util.Objects;

public class SaveScriptsAction extends BarAction implements Initialisable {

    @Override
    public void initialised() {
        getDiveCenter().properties().unsavedProofScripts.addObserver(x -> setEnabled(x));
        setEnabled(false);
    }

    @Override
    public void actionPerformed(ActionEvent ev) {
        try {
            getDiveCenter().getProjectManager().saveProofScripts();
            getDiveCenter().properties().unsavedProofScripts.setValue(false);
            getDiveCenter().getMainController().setStatus("Proof scripts successfully saved.");
        } catch (IOException e) {
            ExceptionDialog.showExceptionDialog(getParentFrame(), e);
        }
    }
}
