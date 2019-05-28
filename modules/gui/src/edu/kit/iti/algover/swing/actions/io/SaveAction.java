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
import java.util.Objects;

public class SaveAction extends BarAction implements InitialisingAction {

    @Override
    public void initialised() {
        if (isSaveAndReload()) {
            getDiveCenter().properties().noProjectMode.addObserver(x -> setEnabled(x));
        } else {
            getDiveCenter().properties().unsavedChanges.addObserver(x -> setEnabled(x));
        }

        setEnabled(false);
    }

    @Override
    public void actionPerformed(ActionEvent ev) {
        try {
            getDiveCenter().getMainController().getDafnyCodeController().saveSources();
            getDiveCenter().properties().unsavedChanges.setValue(false);
            getDiveCenter().getMainController().setStatus("Sources successfully saved.");

            if (isSaveAndReload()) {
                getDiveCenter().reloadProject();
            }


        } catch (IOException e) {
            ExceptionDialog.showExceptionDialog(getParentFrame(), e);
        }
    }

    private boolean isSaveAndReload() {
        Object extra = getValue(EXTRA);
        return Objects.equals("saveAndReload", extra);
    }
}
