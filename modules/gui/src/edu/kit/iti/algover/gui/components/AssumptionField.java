package edu.kit.iti.algover.gui.components;

import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.TopFormula;

import javax.swing.*;
import java.util.List;

/**
 * Created by sarah on 10/25/16.
 */
public class AssumptionField extends JTextArea {

    String text = "";
    public AssumptionField(PVC pvc){

        List<TopFormula> assumptions = pvc.getAssumptionsWithInfo();
        for(TopFormula f: assumptions){
            text += f.getTerm().toString()+"\n";
        }
        this.setText(text);
        //this.setEditable(false);
        this.setVisible(true);
    }


}
