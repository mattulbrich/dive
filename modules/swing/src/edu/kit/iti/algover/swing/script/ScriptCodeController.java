/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.swing.script;

import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofStatus;
import edu.kit.iti.algover.swing.DiveCenter;
import edu.kit.iti.algover.swing.code.DafnyTokenMaker;
import edu.kit.iti.algover.swing.script.ProofNodeCheckpoint.Type;
import edu.kit.iti.algover.swing.util.GUIUtil;
import edu.kit.iti.algover.swing.util.Log;
import edu.kit.iti.algover.swing.util.Property;
import edu.kit.iti.algover.swing.util.Settings;
import edu.kit.iti.algover.swing.util.UnifyingDocumentListener;
import edu.kit.iti.algover.util.ExceptionDetails;
import edu.kit.iti.algover.util.ExceptionDetails.ExceptionReportInfo;
import org.fife.ui.rsyntaxtextarea.AbstractTokenMakerFactory;
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea;
import org.fife.ui.rsyntaxtextarea.SquiggleUnderlineHighlightPainter;
import org.fife.ui.rsyntaxtextarea.TokenMakerFactory;
import org.fife.ui.rtextarea.RTextScrollPane;

import javax.swing.*;
import javax.swing.event.CaretEvent;
import javax.swing.event.DocumentEvent;
import javax.swing.text.AttributeSet;
import javax.swing.text.BadLocationException;
import javax.swing.text.Highlighter;
import javax.swing.text.Highlighter.HighlightPainter;
import javax.swing.text.SimpleAttributeSet;
import java.awt.*;
import java.io.IOException;
import java.util.List;

public class ScriptCodeController {

    private static final Settings S = Settings.getInstance();

    private static final Color WARN_BACKGROUND =
            S.getColor("dive.scriptlabel.warnbackground", Color.orange);

    private static final Color SUCCESS_BACKGROUND =
            S.getColor("dive.scriptlabel.successbackground", Color.green);

    private static final Color DIRTY_BACKGROUND =
            S.getColor("dive.scriptlabel.dirtybackground", Color.lightGray);

    private static final HighlightPainter SQUIGGLY_HIGHLIGHT =
            new SquiggleUnderlineHighlightPainter(Color.red);

    private static final HighlightPainter SPOT_HIGHLIGHT =
            new SpotHighlightPainter(Color.orange, "_"/*"\u25b6"*/);

    private static final HighlightPainter OPEN_SPOT_HIGHLIGHT =
            new SpotHighlightPainter(Color.red, "X");

    private static final HighlightPainter BRANCH_HIGHLIGHT =
            new SpotHighlightPainter(Color.BLUE, "\u2225"/*"\u25c0"*/);

    private static final HighlightPainter CLOSED_HIGHLIGHT =
            new SpotHighlightPainter(Color.green.darker(), "\u25cf");

    static {
        AbstractTokenMakerFactory atmf = (AbstractTokenMakerFactory) TokenMakerFactory.getDefaultInstance();
        atmf.putMapping("text/dafny-script", ScriptTokenMaker.class.getName());
    }

    private final DiveCenter diveCenter;
    private final JLabel label;

    private JPanel component;
    private RSyntaxTextArea textArea;
    private boolean documentChangeListenerActive = true;
    private List<ProofNodeCheckpoint> checkPoints;
    private Proof proof;

    public ScriptCodeController(DiveCenter diveCenter) throws IOException {
        this.diveCenter = diveCenter;
        diveCenter.properties().activePVC.addObserver(this::setPVC);
        diveCenter.properties().insertIntoScriptCaret.addObserver(this::insertAtCaret);
        // not supported yet
        // diveCenter.properties().insertIntoScriptCommand.addObserver(this::insertAtCommand);

        this.component = new JPanel(new BorderLayout());
        {
            JPanel topPanel = new JPanel(new BorderLayout());
            {
                this.label = new JLabel();
                this.label.setOpaque(true);
                label.setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5));
                topPanel.add(label, BorderLayout.CENTER);
            }
            try {
                Action action = diveCenter.getBarManager().makeAction("proof.replay");
                JButton b = new JButton(action);
                topPanel.add(b, BorderLayout.EAST);
            } catch (IOException e) {
                Log.stacktrace(Log.DEBUG, e);
            }
            component.add(topPanel, BorderLayout.NORTH);
        }
        {
            this.textArea = new RSyntaxTextArea();
            UnifyingDocumentListener listener = new UnifyingDocumentListener(this::docChanged);
            textArea.getDocument().addDocumentListener(listener);
            String keyStrokeAndKey = "control ENTER";
            KeyStroke keyStroke = KeyStroke.getKeyStroke(keyStrokeAndKey);
            textArea.getInputMap().put(keyStroke, keyStrokeAndKey);
            textArea.getActionMap().put(keyStrokeAndKey,
                    diveCenter.getMainController().getBarManager().makeAction("proof.replay"));
            textArea.addCaretListener(this::caretUpdated);
            textArea.setSyntaxEditingStyle("text/dafny-script");
            JPopupMenu popup = textArea.getPopupMenu();
            popup.insert(new JPopupMenu.Separator(), 0);
            popup.insert(diveCenter.getBarManager().makeAction("proof.insertBranches"), 0);
            component.add(new RTextScrollPane(textArea));
        }
        setPVC(null);
    }

    private void insertAtCaret(String text) {
        textArea.insert(text, textArea.getCaretPosition());
    }

    private void insertAtCommand(String text) {
        ProofNodeCheckpoint checkPt = diveCenter.properties().proofNodeCheckpoint.getValue();
        int line = checkPt.getLine();
        int col = checkPt.getColumn();
        try {
            int pos = textArea.getLineStartOffset(line) + col;
            textArea.insert(text, pos);
        } catch (BadLocationException e) {
            e.printStackTrace();
            insertAtCaret(text);
        }
    }

    private void caretUpdated(CaretEvent ev) {
        if (checkPoints == null || proof == null) {
            return;
        }

        // find the last check point that has been passed.
        int pos = textArea.getCaret().getDot();
        ProofNodeCheckpoint last = null;
        for (ProofNodeCheckpoint checkPoint : checkPoints) {
            int checkPos = GUIUtil.linecolToPos(textArea, checkPoint.getLine(), checkPoint.getColumn() - 1);
            if (pos > checkPos) {
                last = checkPoint;
            }
        }

        if (last != null) {
            diveCenter.properties().proofNodeCheckpoint.setValue(last);
        }
    }

    private void docChanged(DocumentEvent ev) {
        if (!documentChangeListenerActive) {
            return;
        }

        PVC pvc = diveCenter.properties().activePVC.getValue();
        if (pvc == null) {
            return;
        }
        String id = pvc.getIdentifier();
        Proof proof = diveCenter.getProjectManager().getProofForPVC(id);
        proof.setScriptText(textArea.getText());
        textArea.getHighlighter().removeAllHighlights();
        checkPoints = null;
        // This is similar to a proof that has finished: Change in the
        // proof status
        diveCenter.properties().onGoingProof.fire(false);
        diveCenter.properties().unsavedProofScripts.setValue(true);
        setLabelText(proof.getProofStatus());
        diveCenter.getMainController().setStatus("Script modified.");
    }

    private void setPVC(PVC pvc) {

        if (pvc == null) {
            textArea.setEnabled(false);
            textArea.setEditable(false);
            label.setText("No proof selected");
            this.proof = null;
        } else {
            textArea.setEnabled(true);
            textArea.setEditable(true);
            String id = pvc.getIdentifier();

            this.proof = diveCenter.getProjectManager().getProofForPVC(id);

            ProofNode root = proof.getProofRoot();
            if (root == null) {
                root = ProofNode.createRoot(pvc);
            }

            documentChangeListenerActive = false;
            textArea.setText(proof.getScriptText());
            documentChangeListenerActive = true;
            textArea.setCaretPosition(0);
            setProofState(proof);

            diveCenter.properties().proofNodeCheckpoint.setValue(
                    new ProofNodeCheckpoint(root, 1, 1, Type.OPEN));
        }
    }

    private void setProofState(Proof proof) {
        setLabelText(proof.getProofStatus());

        Highlighter highlighter = textArea.getHighlighter();
        highlighter.removeAllHighlights();
        List<Exception> failures = proof.getFailures();
        if (failures != null && !failures.isEmpty()) {
            // TODO Deal with several failures ?!
            Exception exc = failures.get(0);
            Log.stacktrace(exc);
            diveCenter.getMainController().setStatus(exc);
            ExceptionReportInfo report = ExceptionDetails.extractReportInfo(exc);
            if (report.getLine() >= 0) {
                int pos = GUIUtil.linecolToPos(textArea, report.getLine(), report.getColumn());

                try {
                    highlighter.addHighlight(pos, pos + report.getLength(), SQUIGGLY_HIGHLIGHT);
                } catch (BadLocationException e) {
                    e.printStackTrace();
                }
            }
        }
        checkPoints = ProofNodeCheckpoint.extractCheckpoints(proof);
        addHandles();
    }

    private void addHandles() {
        Highlighter highlighter = textArea.getHighlighter();
        String text = textArea.getText();
        for (ProofNodeCheckpoint checkPoint : checkPoints) {
            int caretPos = GUIUtil.linecolToPos(textArea, checkPoint.getLine(), checkPoint.getColumn());
            try {
                HighlightPainter color;
                switch (checkPoint.getType()) {
                case OPEN:
                    color = OPEN_SPOT_HIGHLIGHT;
                    break;
                case CALL:
                    // give the symbol chance to not be on a character.
                    // caretPos = Math.max(0, caretPos - 1);
                    color = SPOT_HIGHLIGHT;
                    break;
                case BRANCH:
                    color = BRANCH_HIGHLIGHT;
                    break;
                case CLOSED:
                    color = CLOSED_HIGHLIGHT;
                    break;
                default:
                    throw new Error("unreachable");
                }
                highlighter.addHighlight(caretPos, caretPos, color);
            } catch (BadLocationException e) {
                e.printStackTrace();
            }
        }
        textArea.repaint();
    }

    public void replay() {
        PVC pvc = diveCenter.properties().activePVC.getValue();
        String id = pvc.getIdentifier();
        Proof proof = diveCenter.getProjectManager().getProofForPVC(id);
        proof.setScriptTextAndInterpret(textArea.getText());
        setProofState(proof);
        caretUpdated(null);
    }

    private void setLabelText(ProofStatus proofStatus) {
        switch (proofStatus) {
        case OPEN:
            label.setText("Proof does not fail, but has open goals.");
            label.setBackground(WARN_BACKGROUND);
            break;
        case FAILING:
            label.setText("Proof fails while parsing or replaying.");
            label.setBackground(WARN_BACKGROUND);
            break;
        case CLOSED:
            label.setText("Proof successfully closed.");
            label.setBackground(SUCCESS_BACKGROUND);
            break;
        case NON_EXISTING:
            label.setText("There is no proof, yet.");
            label.setBackground(DIRTY_BACKGROUND);
            break;
        case CHANGED_SCRIPT:
            label.setText("Proof script has changed since last replay.");
            label.setBackground(DIRTY_BACKGROUND);
            break;
        }
    }


    public Component getComponent() {
        return component;
    }

    public void insertAt(int line, int column, String str) {
        try {
            int pos = GUIUtil.linecolToPos(textArea, line, column);
            textArea.getDocument().insertString(pos, str, new SimpleAttributeSet());
        } catch (BadLocationException e) {
            Log.log(Log.DEBUG, "Error in index computation");
            Log.stacktrace(Log.DEBUG, e);
        }
    }
}
