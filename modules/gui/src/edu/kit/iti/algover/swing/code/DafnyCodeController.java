/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *  
 */

package edu.kit.iti.algover.swing.code;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.swing.DiveCenter;
import edu.kit.iti.algover.swing.code.DafnyTokenMaker;
import edu.kit.iti.algover.swing.util.ExceptionDialog;
import edu.kit.iti.algover.swing.util.GUIUtil;
import edu.kit.iti.algover.swing.util.Log;
import edu.kit.iti.algover.swing.util.Settings;
import edu.kit.iti.algover.swing.util.UnifyingDocumentListener;
import edu.kit.iti.algover.symbex.AssertionElement;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.PathConditionElement.AssumptionType;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.util.ExceptionDetails;
import edu.kit.iti.algover.util.ExceptionDetails.ExceptionReportInfo;
import edu.kit.iti.algover.util.Util;
import org.antlr.runtime.Token;
import org.fife.ui.rsyntaxtextarea.AbstractTokenMakerFactory;
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea;
import org.fife.ui.rsyntaxtextarea.SquiggleUnderlineHighlightPainter;
import org.fife.ui.rsyntaxtextarea.TokenMakerFactory;
import org.fife.ui.rtextarea.RTextScrollPane;

import javax.swing.*;
import javax.swing.event.DocumentEvent;
import javax.swing.text.BadLocationException;
import javax.swing.text.DefaultHighlighter.DefaultHighlightPainter;
import javax.swing.text.Highlighter.HighlightPainter;
import java.awt.*;
import java.io.File;
import java.io.IOException;
import java.lang.System.Logger.Level;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

public class DafnyCodeController {
    private static final Color SQUIGGLY_LINES_COLOR =
            Settings.getInstance().getColor("dive.codearea.squigglylinescolor", Color.red);

    private static final HighlightPainter SQUIGGLY_LINES =
            new SquiggleUnderlineHighlightPainter(SQUIGGLY_LINES_COLOR);

    public static final String FILENAME = "filename";

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
        diveCenter.properties().activePVC.addObserver(this::updatePVC);
    }

    private void updatePVC(PVC pvc) {
        SymbexPath symbexPath = pvc.getPathThroughProgram();
        if (symbexPath == null) {
            return;
        }
        String filename = pvc.getDeclaration().getFilename();
        int tabIndex = getIndexByFilename(filename);
        RSyntaxTextArea textArea =
                GUIUtil.findComponent(tabs.getComponentAt(tabIndex), RSyntaxTextArea.class);

        textArea.getHighlighter().removeAllHighlights();

        PVCHighlighting.updateHighlight(symbexPath, textArea);
    }

    private void updateProject(Project project) {

        if (project == null) {
            // Never mind. I will stick to the existing panes.
            return;
        }

        List<File> files = project.getConfiguration().getDafnyFiles();

        // close tabs
        for (int i = 0; i < tabs.getTabCount(); i++) {
            JComponent tab = (JComponent) tabs.getComponentAt(i);
            String filename = (String) tab.getClientProperty(FILENAME);
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
                addTab(file);
            } catch (IOException e) {
                ExceptionDialog.showExceptionDialog(diveCenter.getMainWindow(),
                        "Cannot open file " + file, e);
            }
        }

    }

    private void addTab(File file) throws IOException {
        RSyntaxTextArea rsta = new RSyntaxTextArea();
        RTextScrollPane scroll = new RTextScrollPane(rsta);
        rsta.setText(Util.readFileAsString(file));
        rsta.setSyntaxEditingStyle("text/dafny");
        rsta.getDocument().addDocumentListener(new UnifyingDocumentListener(this::codeChanged));
        scroll.putClientProperty(FILENAME, file.toString());
        tabs.addTab(file.getName(), scroll);
    }

    private void codeChanged(DocumentEvent e) {
        for (int i = 0; i < tabs.getTabCount(); i++) {
            RSyntaxTextArea textArea = GUIUtil.findComponent(tabs.getComponentAt(i), RSyntaxTextArea.class);
            textArea.getHighlighter().removeAllHighlights();
        }
        diveCenter.properties().noProjectMode.setValue(true);
        diveCenter.properties().unsavedChanges.setValue(true);
        setException(null);
        diveCenter.getMainController().setStatus("Sources have been modified. Disabling prover.");
    }

    public Component getComponent() {
        return tabs;
    }

    public void saveSources() throws IOException {
        for (int i = 0; i < tabs.getTabCount(); i++) {
            JComponent tab = (JComponent) tabs.getComponentAt(i);
            String filename = (String) tab.getClientProperty(FILENAME);
            RSyntaxTextArea textArea = GUIUtil.findComponent(tab, RSyntaxTextArea.class);
            Util.saveStringAsFile(textArea.getText(), new File(filename));
        }
    }

    public void setException(Exception exc) {
        for (int i = 0; i < tabs.getTabCount(); i++) {
            RSyntaxTextArea textArea = GUIUtil.findComponent(tabs.getComponentAt(i), RSyntaxTextArea.class);
            textArea.getHighlighter().removeAllHighlights();
        }

        if (exc == null) {
            return;
        }

        ExceptionReportInfo report = ExceptionDetails.extractReportInfo(exc);
        String filename = report.getFilename();
        if (filename == null) {
            return;
        }

        int index = getIndexByFilename(filename);
        if (index < 0) {
            Log.log(Log.DEBUG,
               "File with error not found in tabs: " +
                       filename);
            try {
                addTab(new File(filename));
            } catch (IOException e) {
                ExceptionDialog.showExceptionDialog(diveCenter.getMainWindow(), e);
            }
            index = tabs.getTabCount() - 1;
        }

        tabs.setSelectedIndex(index);
        Component container = tabs.getComponentAt(index);
        RSyntaxTextArea textArea = GUIUtil.findComponent(container, RSyntaxTextArea.class);
        try {
            int pos = GUIUtil.linecolToPos(textArea.getText(), report.getLine(), report.getColumn());
            Object hilight = textArea.getHighlighter().addHighlight(pos, pos+report.getLength(), SQUIGGLY_LINES);
            textArea.putClientProperty("exception-highlight", hilight);
        } catch (BadLocationException e) {
            Log.stacktrace(Log.DEBUG, e);
        }
    }

    private int getIndexByFilename(String filename) {
       for (int i = 0; i < tabs.getTabCount(); i++) {
           JComponent tab = (JComponent) tabs.getComponentAt(i);
           String property = (String) tab.getClientProperty(FILENAME);
           if(Objects.equals(filename, property)) {
               return i;
           }
       }
       return -1;
    }
}
