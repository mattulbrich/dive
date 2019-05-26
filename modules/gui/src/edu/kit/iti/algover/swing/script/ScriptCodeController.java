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
import edu.kit.iti.algover.swing.DiveCenter;
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea;

import java.awt.*;

public class ScriptCodeController {

    private final DiveCenter diveCenter;

    private RSyntaxTextArea component = new RSyntaxTextArea();

    public ScriptCodeController(DiveCenter diveCenter) {
        this.diveCenter = diveCenter;

        diveCenter.activePVC.addObserver(this::setPVC);
    }

    private void setPVC(PVC pvc) {

        String id = pvc.getIdentifier();

        Proof proof = diveCenter.getProjectManager().getProofForPVC(id);
        proof.interpretScript();

        ProofNode root = proof.getProofRoot();

        component.setText(proof.getScript());
        component.setCaretPosition(0);

        diveCenter.proofNode.setValue(root);
    }


    public Component getComponent() {
        return component;
    }
}
