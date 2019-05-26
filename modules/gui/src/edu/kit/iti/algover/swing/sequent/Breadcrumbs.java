/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.swing.sequent;

import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.swing.DiveCenter;

import javax.swing.*;
import java.awt.*;

public class Breadcrumbs extends JPanel {

    private static final Font LABEL_FONT = new Font("sans-serif", Font.PLAIN, 12);
    private final DiveCenter center;
    private final JLabel classLabel;
    private final JLabel methLabel;
    private final JLabel pvcLabel;

    public Breadcrumbs(DiveCenter center) {
        this.center = center;
        center.activePVC.addObserver(this::setPVC);

        {
            this.classLabel = new JLabel();
            classLabel.setFont(LABEL_FONT);
            add(classLabel);
        }
        add(new JLabel(" > "));
        {
            this.methLabel = new JLabel();
            methLabel.setFont(LABEL_FONT);
            add(methLabel);
        }
        add(new JLabel(" > "));
        {
            this.pvcLabel = new JLabel();
            pvcLabel.setFont(LABEL_FONT);
            add(pvcLabel);
        }
    }

    private void setPVC(PVC pvc) {
        String id = pvc.getIdentifier();
        int slash = id.indexOf('/');
        String classMeth = id.substring(0, slash);
        int dot = classMeth.indexOf('.');
        if (dot > 0) {
            String clss = classMeth.substring(0, dot);
            classLabel.setText(clss);
        } else {
            classLabel.setText("<html><i>no class</i>");
        }
        String meth = classMeth.substring(dot + 1);
        methLabel.setText(meth);

        pvcLabel.setText(id.substring(slash + 1));
    }

}
