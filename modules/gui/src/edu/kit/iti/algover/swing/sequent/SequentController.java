/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.swing.sequent;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.rules.TermSelector.SequentPolarity;
import edu.kit.iti.algover.swing.DiveCenter;
import edu.kit.iti.algover.swing.script.ProofNodeCheckpoint;
import edu.kit.iti.algover.swing.script.ProofNodeCheckpoint.Type;
import edu.kit.iti.algover.swing.util.GUIUtil;
import edu.kit.iti.algover.swing.util.IndentationLayout;
import edu.kit.iti.algover.swing.util.Settings;
import edu.kit.iti.algover.term.Sequent;

import javax.swing.*;
import java.awt.*;

public class SequentController {

    private final static SequentSeparator SEPARATOR = new SequentSeparator();
    public static final String BACKGROUND = "dive.sequentview.background";
    private static final Icon BULLET =
            GUIUtil.makeIcon(SequentController.class.getResource("img/bullet_black.png"));

    private final JPanel componnent;
    private final JPanel seqComponent;
    private DiveCenter diveCenter;

    public SequentController(DiveCenter diveCenter) {
        this.diveCenter = diveCenter;

        componnent = new JPanel(new BorderLayout());
        // componnent.add(new Breadcrumbs(diveCenter), BorderLayout.NORTH);

        seqComponent = new JPanel(new IndentationLayout(SEPARATOR.SEP_LENGTH / 2));
        seqComponent.setBackground(Settings.getInstance().getColor(BACKGROUND, Color.WHITE));
        seqComponent.setBorder(BorderFactory.createEmptyBorder(10,10,10,10));
        componnent.add(seqComponent);

        diveCenter.properties().proofNodeCheckpoint.addObserver(this::setProofNode);
        setProofNode(null);
    }

    private void setProofNode(ProofNodeCheckpoint checkpoint) {

        seqComponent.removeAll();

        if (checkpoint == null) {
            seqComponent.add(new JLabel("No sequent to display."));
            seqComponent.revalidate();
            seqComponent.repaint();
            return;
        }

        if(checkpoint.getType() == Type.BRANCH) {
            // Show a button to add the cases.
            seqComponent.add(new JLabel("More than one open branch at this point:"));
            for (ProofNode child : checkpoint.getProofNode().getChildren()) {
                seqComponent.add(new JLabel(child.getLabel(), BULLET, JLabel.LEFT));
            }
            seqComponent.add(new JButton(diveCenter.getBarManager().getAction("proof.insertBranches")));
            seqComponent.revalidate();
            seqComponent.repaint();
            return;
        }

        ProofNode proofNode = checkpoint.getProofNode();
        Sequent sequent = proofNode.getSequent();
        int i = 0;
        for (ProofFormula pf : sequent.getAntecedent()) {
            TermSelector termSelector = new TermSelector(SequentPolarity.ANTECEDENT, i);
            TermController ctrl = new TermController(diveCenter, pf, termSelector);
            seqComponent.add(ctrl.getComponent());
            i++;
        }

        seqComponent.add(SEPARATOR);

        i = 0;
        for (ProofFormula pf : sequent.getSuccedent()) {
            TermSelector termSelector = new TermSelector(SequentPolarity.SUCCEDENT, i);
            TermController ctrl = new TermController(diveCenter, pf, termSelector);
            seqComponent.add(ctrl.getComponent());
            i++;
        }

        seqComponent.revalidate();
        seqComponent.repaint();

    }

    public Component getComponent() {
        return componnent;
    }
}
