/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */
package edu.kit.iti.algover.swing.actions.io;

import java.awt.event.ActionEvent;
import java.io.File;

import javax.swing.JFileChooser;
import javax.swing.filechooser.FileFilter;
import javax.swing.filechooser.FileNameExtensionFilter;

import edu.kit.iti.algover.swing.DiveCenter;
import edu.kit.iti.algover.swing.Main;
import edu.kit.iti.algover.swing.actions.BarAction;
import edu.kit.iti.algover.swing.actions.BarManager.Initialisable;
import edu.kit.iti.algover.swing.util.ExceptionDialog;
import edu.kit.iti.algover.swing.util.Log;

/**
 * This is the action to load a problem file.
 *
 * It is embedded into the menu.
 */
@SuppressWarnings("serial")
public class OpenAction extends BarAction implements Initialisable {

    private static final FileFilter DFY_FILTER =
            new FileNameExtensionFilter("Dafny files", "dfy");

    private static final FileFilter XML_FILTER =
            new FileNameExtensionFilter("Project configurations", "xml");

    @Override
    public void initialised() {
        DiveCenter proofCenter = getDiveCenter();
        if(proofCenter != null) {
            proofCenter.properties().onGoingProof.addObserver(ongoing -> setEnabled(!ongoing));
        }
    }

    @Override
    public void actionPerformed(ActionEvent e) {

        JFileChooser fileChooser = new JFileChooser(".");

        fileChooser.addChoosableFileFilter(DFY_FILTER);
        fileChooser.addChoosableFileFilter(XML_FILTER);

        int result = fileChooser.showOpenDialog(getParentFrame());
        if(result == JFileChooser.APPROVE_OPTION) {
            File selectedFile = fileChooser.getSelectedFile();
            try {
                Main.openDiveCenter(selectedFile);
            } catch(Exception ex) {
                Log.log(Log.DEBUG, ex);
                ExceptionDialog.showExceptionDialog(getParentFrame(), ex);
            }
        }
    }
}
