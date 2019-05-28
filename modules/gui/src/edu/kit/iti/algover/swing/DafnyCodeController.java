/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *  
 */

package edu.kit.iti.algover.swing;

import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.swing.code.DafnyTokenMaker;
import edu.kit.iti.algover.swing.util.ExceptionDialog;
import edu.kit.iti.algover.swing.util.GUIUtil;
import edu.kit.iti.algover.swing.util.UnifyingDocumentListener;
import edu.kit.iti.algover.util.Util;
import org.fife.ui.rsyntaxtextarea.AbstractTokenMakerFactory;
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea;
import org.fife.ui.rsyntaxtextarea.TokenMakerFactory;
import org.fife.ui.rtextarea.RTextScrollPane;

import javax.swing.*;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import java.awt.*;
import java.beans.PropertyChangeEvent;
import java.io.File;
import java.io.IOException;
import java.util.List;

public class DafnyCodeController {
    private DiveCenter diveCenter;

    private JTabbedPane tabs;

    static {
        AbstractTokenMakerFactory atmf = (AbstractTokenMakerFactory) TokenMakerFactory.getDefaultInstance();
        atmf.putMapping("text/dafny", DafnyTokenMaker.class.getName());
    }

    public DafnyCodeController(DiveCenter diveCenter) {
        this.diveCenter = diveCenter;
        this.tabs = new JTabbedPane();

        diveCenter.properties().project.addObserver(this::updateProject);
    }

    private void updateProject(Project project) {

        if (project == null) {
            // Never mind. I will stick to the existing panes.
            return;
        }

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
                rsta.setSyntaxEditingStyle("text/dafny");
                rsta.getDocument().addDocumentListener(new UnifyingDocumentListener(this::codeChanged));
                tabs.addTab(file.getName(), scroll);
            } catch (IOException e) {
                ExceptionDialog.showExceptionDialog(diveCenter.getMainWindow(),
                        "Cannot open file " + file, e);
            }
        }

    }

    private void codeChanged(DocumentEvent e) {
        diveCenter.properties().sourcesModified.setValue(true);
        diveCenter.properties().unsavedChanges.setValue(true);
    }

    public Component getComponent() {
        return tabs;
    }

    public void saveSources() throws IOException {
        for (int i = 0; i < tabs.getTabCount(); i++) {
            JComponent tab = (JComponent) tabs.getTabComponentAt(i);
            String filename = (String) tab.getClientProperty("filename");
            RSyntaxTextArea textArea = GUIUtil.findComponent(tab, RSyntaxTextArea.class);
            Util.saveStringAsFile(textArea.getText(), new File(filename));
        }
    }
}
