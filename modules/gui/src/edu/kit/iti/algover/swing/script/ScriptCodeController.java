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
import edu.kit.iti.algover.swing.util.Log;
import edu.kit.iti.algover.swing.util.Settings;
import edu.kit.iti.algover.swing.util.UnifyingDocumentListener;
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea;
import org.fife.ui.rtextarea.RTextScrollPane;

import javax.swing.*;
import javax.swing.event.DocumentEvent;
import java.awt.*;
import java.io.IOException;

public class ScriptCodeController {

    private static final Settings S = Settings.getInstance();

    private static final Color WARN_BACKGROUND =
            S.getColor("dive.scriptlabel.warnbackground", Color.orange);

    private static final Color SUCCESS_BACKGROUND =
            S.getColor("dive.scriptlabel.successbackground", Color.green);

    private static final Color DIRTY_BACKGROUND =
            S.getColor("dive.scriptlabel.dirtybackground", Color.lightGray);

    private final DiveCenter diveCenter;
    private final JLabel label;

    private JPanel component;
    private RSyntaxTextArea textArea = new RSyntaxTextArea();
    private boolean documentChangeListenerActive = true;

    public ScriptCodeController(DiveCenter diveCenter) {
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
            this.textArea.getDocument().addDocumentListener(listener);
            component.add(new RTextScrollPane(textArea));
        }
        setPVC(null);
    }

    private void docChanged(DocumentEvent ev) {
        if (!documentChangeListenerActive) {
            return;
        }

        PVC pvc = diveCenter.properties().activePVC.getValue();
        String id = pvc.getIdentifier();
        Proof proof = diveCenter.getProjectManager().getProofForPVC(id);
        proof.setScriptText(textArea.getText());
        // This is similar to a proof that has finished: Change in the
        // proof status
        diveCenter.properties().onGoingProof.fire(false);
        setLabelText(proof.getProofStatus());
    }

    private void setPVC(PVC pvc) {

        if (pvc == null) {
            textArea.setEnabled(false);
            textArea.setEditable(false);
            label.setText("No proof selected");
        } else {
            textArea.setEnabled(true);
            textArea.setEditable(true);
            String id = pvc.getIdentifier();

            Proof proof = diveCenter.getProjectManager().getProofForPVC(id);

            ProofNode root = proof.getProofRoot();
            if (root == null) {
                root = ProofNode.createRoot(pvc);
            }

            documentChangeListenerActive = false;
            textArea.setText(proof.getScript());
            documentChangeListenerActive = true;
            textArea.setCaretPosition(0);

            setLabelText(proof.getProofStatus());

            diveCenter.properties().proofNode.setValue(root);
        }
    }

    public void replay() {
        PVC pvc = diveCenter.properties().activePVC.getValue();
        String id = pvc.getIdentifier();
        Proof proof = diveCenter.getProjectManager().getProofForPVC(id);
        proof.setScriptTextAndInterpret(textArea.getText());
        setLabelText(proof.getProofStatus());
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
