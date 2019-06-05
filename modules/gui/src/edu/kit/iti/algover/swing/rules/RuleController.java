/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.swing.rules;

import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.swing.util.IndentationLayout;

import javax.swing.*;
import javax.swing.border.Border;
import java.awt.*;

public class RuleController {
    private ProofRule proofRule;

    public RuleController(ProofRule proofRule) {
        this.proofRule = proofRule;
    }

    public Component getComponent() {

        JPanel result = new JPanel(new FlowLayout(FlowLayout.LEFT));

        result.setBorder(BorderFactory.createEtchedBorder());
        result.setBackground(Color.white);
        result.add(new JLabel(proofRule.getName()));
        JLabel branches = new JLabel("\u27bd2");
        branches.setToolTipText("Click to refine");
        result.add(branches);
        JTextArea descr = new JTextArea("Split the proof obligation into 2 or more subgoals");
        descr.setForeground(Color.GRAY);
        descr.setEditable(false);
        result.add(descr);
        result.putClientProperty(IndentationLayout.INDENTED_PROPERTY, true);
        return result;
    }
}
