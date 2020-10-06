///*
// * This file is part of AlgoVer.
// *
// * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
// *
// */
//
//package edu.kit.iti.algover.swing.actions.io;
//
//import edu.kit.iti.algover.parser.DafnyException;
//import edu.kit.iti.algover.parser.DafnyParserException;
//import edu.kit.iti.algover.project.ProjectManager;
//import edu.kit.iti.algover.swing.code.DafnyCodeController;
//import edu.kit.iti.algover.swing.DiveProperties;
//import edu.kit.iti.algover.swing.MainController;
//import edu.kit.iti.algover.swing.actions.BarAction;
//import edu.kit.iti.algover.swing.actions.BarManager.Initialisable;
//import edu.kit.iti.algover.swing.util.ExceptionDialog;
//import edu.kit.iti.algover.swing.util.Log;
//import edu.kit.iti.algover.util.FormatException;
//
//import java.awt.event.ActionEvent;
//import java.io.IOException;
//import java.util.Objects;
//
//public class SaveAndReloadAction extends BarAction implements Initialisable {
//
//    @Override
//    public void initialised() {
//        getDiveCenter().properties().noProjectMode.addObserver(x -> setEnabled(x));
//        setEnabled(false);
//    }
//
//    @Override
//    public void actionPerformed(ActionEvent ev) {
//        MainController mainController = getDiveCenter().getMainController();
//        DiveProperties diveProperties = getDiveCenter().properties();
//        DafnyCodeController codeCtrl = mainController.getDafnyCodeController();
//        ProjectManager projectManager = getDiveCenter().getProjectManager();
//
//        try {
//            // that's the same as in SaveAction
//            codeCtrl.saveSources();
//            diveProperties.unsavedChanges.setValue(false);
//
//
//        } catch (IOException e) {
//            ExceptionDialog.showExceptionDialog(getParentFrame(), e);
//        }
//    }
//
//    }
//}
