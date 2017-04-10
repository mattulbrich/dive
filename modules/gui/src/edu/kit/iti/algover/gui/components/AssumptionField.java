package edu.kit.iti.algover.gui.components;

import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.TopFormula;

import javax.swing.*;
import javax.swing.border.EtchedBorder;
import javax.swing.border.TitledBorder;
import java.util.List;

/**
 * Created by sarah on 10/25/16.
 */
public class AssumptionField extends JPanel {

    String text = "";
    public AssumptionField(PVC pvc){
        this.setBorder(new TitledBorder("Aussumptions"));
        this.setLayout(new BoxLayout(this, BoxLayout.PAGE_AXIS));
        List<TopFormula> assumptions = pvc.getAssumptionsWithInfo();
        for(TopFormula f: assumptions){
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
