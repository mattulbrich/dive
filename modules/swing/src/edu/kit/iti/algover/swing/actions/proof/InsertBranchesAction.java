/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.swing.actions.proof;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.BranchInfo;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.swing.actions.BarAction;
import edu.kit.iti.algover.swing.actions.BarManager.Initialisable;
import edu.kit.iti.algover.swing.script.ProofNodeCheckpoint;
import edu.kit.iti.algover.swing.script.ProofNodeCheckpoint.Type;
import edu.kit.iti.algover.swing.util.Log;

import javax.swing.*;
import java.awt.event.ActionEvent;

public class InsertBranchesAction extends BarAction implements Initialisable {

    public InsertBranchesAction() {
        // initially not enaled.
        setEnabled(false);
    }

    @Override
    public void initialised() {
        getDiveCenter().properties().proofNodeCheckpoint.addObserver(
                cp -> setEnabled(cp.getType() == Type.BRANCH) );
    }

    @Override
    public void actionPerformed(ActionEvent e) {

        ProofNodeCheckpoint cp = getDiveCenter().properties().proofNodeCheckpoint.getValue();
        assert cp.getType() == Type.BRANCH;


        
        getDiveCenter().getMainController().getScriptCodeController()
                .insertAt(cp.getLine(), cp.getColumn(), makeCases(cp));

    }

    private String makeCases(ProofNodeCheckpoint cp) {
        ProofRuleApplication pra = cp.getProofNode().getProofRuleApplication();

        StringBuilder sb = new StringBuilder("\ncases {\n");
        for (ProofNode child : cp.getProofNode().getChildren()) {
            sb.append("  case \"" + child.getLabel() + "\": \n");
        }
        sb.append("}\n");
        return sb.toString();
    }

}
