/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *  
 */

package edu.kit.iti.algover.swing.rules;

import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.swing.DiveCenter;
import edu.kit.iti.algover.swing.util.IndentationLayout;

import javax.swing.*;
import javax.swing.border.Border;
import java.awt.*;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.Flow;

public class RuleBayController {


    private final JPanel thePanel;
    private final JScrollPane theComponent;
    private DiveCenter diveCenter;
    private Map<String, List<ProofRule>>  ruleMap = new HashMap<>();

    public RuleBayController(DiveCenter diveCenter) {
        this.diveCenter = diveCenter;

        thePanel = new JPanel(new IndentationLayout(40));
        thePanel.setBorder(BorderFactory.createEmptyBorder(5,5,5,5));

        theComponent = new JScrollPane(thePanel);
        theComponent.getVerticalScrollBar().setUnitIncrement(16);

        diveCenter.properties().termSelector.addObserver(this::updatePanel);
        diveCenter.properties().activePVC.addObserver(this::pvcChanged);
    }

    private void updatePanel() {
        thePanel.removeAll();

        PVC pvc = diveCenter.properties().activePVC.getValue();
        Project proj = diveCenter.properties().project.getValue();

        // Fake content
        for (String header : ruleMap.keySet()) {
            thePanel.add(newHeader(header));
            List<ProofRule> rules = ruleMap.get(header);
            Collections.sort(rules, (r1,r2) -> r1.getName().compareToIgnoreCase(r2.getName()));
            for (ProofRule proofRule : rules) {
                thePanel.add(new RuleController(diveCenter, proofRule).getComponent());
            }
        }
    }

    private JLabel newHeader(String s) {
        JLabel result = new JLabel(s);
        result.setFont(new Font("Sans serif", Font.BOLD, 14));
        result.setBorder(
                BorderFactory.createCompoundBorder(
                        BorderFactory.createEmptyBorder(10,0,5,0),
                        new UnderlineBorder(Color.black, 2)));
        return result;
    }

    private void pvcChanged(PVC pvc) {

        ruleMap.clear();
        if (pvc == null) {
            return;
        }

        Project proj = diveCenter.properties().project.getValue();
        Collection<ProofRule> allRules = proj.getProofRules(pvc);

        for (ProofRule rule : allRules) {
            String cat = rule.getCategory();
            List<ProofRule> list = ruleMap.get(cat);
            if (list == null) {
                list = new LinkedList<>();
                ruleMap.put(cat, list);
            }
            list.add(rule);
        }

        updatePanel();
    }

    public Component getComponent() {
        return theComponent;
    }
}
