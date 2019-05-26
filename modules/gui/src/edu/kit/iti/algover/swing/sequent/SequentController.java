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
import edu.kit.iti.algover.swing.util.Settings;
import edu.kit.iti.algover.term.Sequent;

import javax.swing.*;
import java.awt.*;

import static java.io.File.separator;

public class SequentController {

    private final static SequentSeparator SEPARATOR = new SequentSeparator();
    public static final String BACKGROUND = "dive.sequentview.background";

    private final JPanel componnent;
    private final JPanel seqComponent;
    private ProofNode proofNode;
    private DiveCenter diveCenter;

    public SequentController(DiveCenter diveCenter) {
        this.diveCenter = diveCenter;

        componnent = new JPanel(new BorderLayout());
        componnent.add(new Breadcrumbs(diveCenter), BorderLayout.NORTH);

        seqComponent = new JPanel(new SequentLayoutManager());
        seqComponent.setBackground(Settings.getInstance().getColor(BACKGROUND, Color.WHITE));
        seqComponent.setBorder(BorderFactory.createEmptyBorder(10,10,10,10));
        componnent.add(seqComponent);

        diveCenter.proofNode.addObserver(this::setProofNode);
        setProofNode(null);
    }

    private void setProofNode(ProofNode proofNode) {

        seqComponent.removeAll();
        this.proofNode = proofNode;

        if (proofNode == null) {
            seqComponent.add(new JLabel("No sequent to display."));
            return;
        }



        Sequent sequent = proofNode.getSequent();

        int i = 0;
        for (ProofFormula pf : sequent.getAntecedent()) {
            TermSelector termSelector = new TermSelector(SequentPolarity.ANTECEDENT, i);
            TermController ctrl = new TermController(diveCenter, pf, termSelector);
            seqComponent.add(ctrl.getComponent());
            i++;
        }

        seqComponent.add(SEPARATOR);
        seqComponent.revalidate();
        seqComponent.repaint();

    }

    public Component getComponent() {
        return componnent;
    }
}
