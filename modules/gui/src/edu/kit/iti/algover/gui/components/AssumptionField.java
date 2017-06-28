/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.gui.components;

import java.util.List;

import javax.swing.BoxLayout;
import javax.swing.JPanel;
import javax.swing.JToolBar;
import javax.swing.border.EtchedBorder;
import javax.swing.border.TitledBorder;

import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.ProofFormula;

/**
 * Created by sarah on 10/25/16.
 */
public class AssumptionField extends JPanel {

    String text = "";
    public AssumptionField(PVC pvc){
        this.setBorder(new TitledBorder("Aussumptions"));
        this.setLayout(new BoxLayout(this, BoxLayout.PAGE_AXIS));
        List<ProofFormula> assumptions = pvc.getSequent().getAntecedent();
        for(ProofFormula f: assumptions){
            CustomFormulaDisplay cfd = new CustomFormulaDisplay(f.getTerm().toString());
            cfd.setToolTipText(f.getTerm().toString());
            cfd.setBorder(new EtchedBorder());
            this.add(cfd);
            this.add(new JToolBar.Separator());
            //text += f.getTerm().toString()+"\n";
        }

        //this.setEditable(false);
        this.setVisible(true);
    }


}
