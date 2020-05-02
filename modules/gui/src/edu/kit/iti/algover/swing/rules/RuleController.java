/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.swing.rules;

import edu.kit.iti.algover.rules.ParameterDescription;
import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.swing.util.IndentationLayout;
import edu.kit.iti.algover.util.Util;

import javax.swing.*;
import javax.swing.border.Border;
import java.awt.*;
import java.util.List;
import java.util.Map.Entry;

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
        JTextArea params = new JTextArea(makeParamString());
        params.setForeground(Color.GRAY);
        params.setEditable(false);
        result.add(params);
        result.putClientProperty(IndentationLayout.INDENTED_PROPERTY, true);
        return result;
    }

    private String makeParamString() {

        List<String> paraList = Util.map(proofRule.getAllParameters().entrySet(), entry ->
                entry.getKey() + ":" + entry.getValue().getType().getName()
        );

        return Util.join(paraList, " ");
    }
}
