/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.swing.rules;

import edu.kit.iti.algover.rules.ParameterDescription;
import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.swing.DiveCenter;
import edu.kit.iti.algover.swing.util.IndentationLayout;
import edu.kit.iti.algover.util.Util;

import javax.swing.*;
import javax.swing.border.Border;
import java.awt.*;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.util.ArrayList;
import java.util.List;
import java.util.Map.Entry;

public class RuleController extends MouseAdapter {

    private static final Font LIGHT_FONT =
            UIManager.getFont("TextArea.font");

    private DiveCenter diveCenter;
    private ProofRule proofRule;

    public RuleController(DiveCenter diveCenter, ProofRule proofRule) {
        this.diveCenter = diveCenter;
        this.proofRule = proofRule;
    }

    public Component getComponent() {

        JPanel result = new JPanel(new FlowLayout(FlowLayout.LEFT));

        result.setBorder(BorderFactory.createEtchedBorder());
        result.setBackground(Color.white);
        result.add(new JLabel(proofRule.getName()));
        JLabel params = new JLabel(makeParamString());
        params.setFont(LIGHT_FONT);
        params.setForeground(Color.GRAY);
        result.add(params);
        result.putClientProperty(IndentationLayout.INDENTED_PROPERTY, true);
        result.addMouseListener(this);
        return result;
    }

    private String makeParamString() {

        List<String> paraList = Util.map(proofRule.getAllParameters().values(),
                param -> {
                    String s = param.getName() + ":" + param.getType().getName();
                    if (!param.isRequired()) {
                        s = "[" + s + "]";
                    }
                    return s;
                }
        );

        return Util.join(paraList, " ");
    }

    @Override
    public void mouseClicked(MouseEvent e) {

        if (e.getClickCount() == 2 && SwingUtilities.isLeftMouseButton(e)) {

            List<String> parts = new ArrayList<>();
            parts.add(proofRule.getName());
            TermSelector termSel = diveCenter.properties().termSelector.getValue();
            for (ParameterDescription<?> param : proofRule.getAllParameters().values()) {
                if (termSel != null && param.getName().equals("on")) {
                    parts.add("on=" + termSel);
                } else if (param.isRequired()) {
                    parts.add(param.getName() + "=");
                }
            }

            String command = Util.join(parts, " ") + ";";

            diveCenter.properties().insertIntoScriptCaret.fire(command);
        }
    }
}
