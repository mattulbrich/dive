/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *  
 */

package edu.kit.iti.algover.swing;

import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.swing.util.ExceptionDialog;
import edu.kit.iti.algover.util.Util;
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea;
import org.fife.ui.rtextarea.RTextScrollPane;

import javax.swing.*;
import java.awt.*;
import java.io.File;
import java.io.IOException;
import java.util.List;

public class DafnyCodeController {
    private DiveCenter diveCenter;

    private JTabbedPane tabs;

    public DafnyCodeController(DiveCenter diveCenter) {
        this.diveCenter = diveCenter;
        this.tabs = new JTabbedPane();

        diveCenter.project.addObserver(this::updateProject);
    }

    private void updateProject(Project project) {

        List<File> files = project.getConfiguration().getDafnyFiles();

        // close tabs
        for (int i = 0; i < tabs.getTabCount(); i++) {
            JComponent tab = (JComponent) tabs.getTabComponentAt(i);
            String filename = (String) tab.getClientProperty("filename");
            File file = new File(filename);
            if(files.contains(file)) {
                files.remove(file);
            } else {
                tabs.removeTabAt(i);
                // compensate for one tab less!
                i--;
            }
        }

        // open tabs
        for (File file : files) {
            try {
                RSyntaxTextArea rsta = new RSyntaxTextArea();
                RTextScrollPane scroll = new RTextScrollPane(rsta);
                rsta.setText(Util.readFileAsString(file));
                tabs.addTab(file.getName(), scroll);
            } catch (IOException e) {
                ExceptionDialog.showExceptionDialog(diveCenter.getMainWindow(),
                        "Cannot open file " + file, e);
            }

        }


    }

    public Component getComponent() {
        return tabs;
    }
}
