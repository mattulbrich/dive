/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */
package edu.kit.iti.algover.swing.actions.io;

import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.swing.DiveCenter;
import edu.kit.iti.algover.swing.Main;
import edu.kit.iti.algover.swing.actions.BarAction;
import edu.kit.iti.algover.swing.actions.BarManager.Initialisable;
import edu.kit.iti.algover.swing.util.ExceptionDialog;
import edu.kit.iti.algover.swing.util.Log;
import edu.kit.iti.algover.util.FormatException;

import javax.swing.*;
import javax.swing.filechooser.FileFilter;
import javax.swing.filechooser.FileNameExtensionFilter;
import java.awt.event.ActionEvent;
import java.io.File;
import java.io.IOException;

/**
 * This is the action to load a problem file.
 *
 * It is embedded into the menu.
 */
@SuppressWarnings("serial")
public class NewFileAction extends BarAction {

    @Override
    public void actionPerformed(ActionEvent e) {
        JFileChooser fileChooser = new JFileChooser(".");

        fileChooser.addChoosableFileFilter(OpenAction.DFY_FILTER);
        fileChooser.addChoosableFileFilter(OpenAction.XML_FILTER);

        int result = fileChooser.showDialog(getParentFrame(), "Create");
        if(result == JFileChooser.APPROVE_OPTION) {
            File selectedFile = fileChooser.getSelectedFile();

            try {
                boolean success = selectedFile.createNewFile();
                if (!success) {
                    ExceptionDialog.showExceptionDialog(getParentFrame(), "The file " +
                            selectedFile + " cannot be created. (Probably because it already exists.)");
                    return;
                }
                Main.openDiveCenter(selectedFile);
            } catch(Exception ex) {
                Log.log(Log.DEBUG, ex);
                ExceptionDialog.showExceptionDialog(getParentFrame(), ex);
            }

        }
    }
}
