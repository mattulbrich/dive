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
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.script.ast.ASTNode;
import edu.kit.iti.algover.script.ast.Position;
import edu.kit.iti.algover.swing.DiveCenter;
import edu.kit.iti.algover.swing.util.GUIUtil;
import edu.kit.iti.algover.swing.util.Log;
import edu.kit.iti.algover.swing.util.Settings;
import edu.kit.iti.algover.swing.util.UnifyingDocumentListener;
import edu.kit.iti.algover.util.ExceptionDetails;
import edu.kit.iti.algover.util.ExceptionDetails.ExceptionReportInfo;
import edu.kit.iti.algover.util.Pair;
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea;
import org.fife.ui.rsyntaxtextarea.SquiggleUnderlineHighlightPainter;
import org.fife.ui.rtextarea.RTextScrollPane;

import javax.swing.*;
import javax.swing.event.CaretEvent;
import javax.swing.event.DocumentEvent;
import javax.swing.text.BadLocationException;
import javax.swing.text.Highlighter;
import javax.swing.text.Highlighter.HighlightPainter;
import java.awt.*;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

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
            new SpotHighlightPainter(Color.orange);

    private static final HighlightPainter OPEN_SPOT_HIGHLIGHT =
            new SpotHighlightPainter(Color.red);

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
            component.add(new RTextScrollPane(textArea));
        }
        setPVC(null);
    }

    private void caretUpdated(CaretEvent ev) {
        System.out.println("ev = [" + ev + "]");
        if (checkPoints == null || proof == null) {
            return;
        }

        // find the last check point that has been passed.
        int pos = ev.getDot();
        ProofNodeCheckpoint last = null;
        for (ProofNodeCheckpoint checkPoint : checkPoints) {
            int checkPos = GUIUtil.linecolToPos(textArea.getText(), checkPoint.position.getLineNumber(), checkPoint.position.getCharInLine() + 1);
            if (pos > checkPos) {
                last = checkPoint;
            }
        }


        try {
            if (last != null) {
                ProofNode node = last.selector.get(proof);
                diveCenter.properties().proofNode.setValue(node);
            }
        } catch (RuleException e) {
            Log.log(Log.DEBUG, "Unexpectedly, a proofnode selector cannot be applied");
            Log.stacktrace(Log.DEBUG, e);
        }

    }

    private void docChanged(DocumentEvent ev) {
        if (!documentChangeListenerActive) {
            return;
        }

        PVC pvc = diveCenter.properties().activePVC.getValue();
        String id = pvc.getIdentifier();
        Proof proof = diveCenter.getProjectManager().getProofForPVC(id);
        proof.setScriptText(textArea.getText());
        textArea.getHighlighter().removeAllHighlights();
        // This is similar to a proof that has finished: Change in the
        // proof status
        diveCenter.properties().onGoingProof.fire(false);
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
            textArea.setText(proof.getScript());
            documentChangeListenerActive = true;
            textArea.setCaretPosition(0);
            setProofState(proof);

            diveCenter.properties().proofNode.setValue(root);
        }
    }

    private void setProofState(Proof proof) {
        setLabelText(proof.getProofStatus());

        Highlighter highlighter = textArea.getHighlighter();
        highlighter.removeAllHighlights();
        String text = textArea.getText();
        Exception exc = proof.getFailException();
        if (exc != null) {
            diveCenter.getMainController().setStatus(exc);
            ExceptionReportInfo report = ExceptionDetails.extractReportInfo(exc);
            int pos = GUIUtil.linecolToPos(text, report.getLine(), report.getColumn());

            try {
                highlighter.addHighlight(pos, pos + report.getLength(), SQUIGGLY_HIGHLIGHT);
            } catch (BadLocationException e) {
                e.printStackTrace();
            }
        } else {
            checkPoints = ProofNodeCheckpointsBuilder.build(proof);
            addHandles();
        }
    }

    private void addHandles() {
        Highlighter highlighter = textArea.getHighlighter();
        String text = textArea.getText();
        for (ProofNodeCheckpoint checkPoint : checkPoints) {
            Position pos = checkPoint.position;
            int caretPos = GUIUtil.linecolToPos(text, pos.getLineNumber(), pos.getCharInLine() + 1);
            if (caretPos > 0 && caretPos < text.length() - 1) {
                caretPos ++;
            }
            try {
                highlighter.addHighlight(caretPos, caretPos + 1, SPOT_HIGHLIGHT);
            } catch (BadLocationException e) {
                e.printStackTrace();
            }
        }
    }

    public void replay() {
        PVC pvc = diveCenter.properties().activePVC.getValue();
        String id = pvc.getIdentifier();
        Proof proof = diveCenter.getProjectManager().getProofForPVC(id);
        proof.setScriptTextAndInterpret(textArea.getText());
        setProofState(proof);
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
        case DIRTY:
            label.setText("Proof has not been replayed since (re)loading.");
            label.setBackground(DIRTY_BACKGROUND);
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
}
