/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.swing.actions.io;

import edu.kit.iti.algover.swing.actions.BarAction;
import edu.kit.iti.algover.swing.actions.BarManager.InitialisingAction;
import edu.kit.iti.algover.swing.util.ExceptionDialog;

import java.awt.event.ActionEvent;
import java.io.IOException;

public class SaveAction extends BarAction implements InitialisingAction {

    @Override
    public void initialised() {
        getDiveCenter().properties().unsavedChanges.addObserver(x -> setEnabled(x));
    }

    @Override
    public void actionPerformed(ActionEvent ev) {
        try {
            getDiveCenter().getMainController().getDafnyCodeController().saveSources();
            getDiveCenter().properties().unsavedChanges.setValue(false);
        } catch (IOException e) {
            ExceptionDialog.showExceptionDialog(getParentFrame(), e);
        }
    }
}
