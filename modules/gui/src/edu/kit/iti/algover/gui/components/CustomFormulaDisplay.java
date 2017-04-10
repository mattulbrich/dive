package edu.kit.iti.algover.gui.components;

import javax.swing.*;
import java.awt.*;

/**
 * Created by sarah on 10/26/16.
 */
public class CustomFormulaDisplay extends JComponent {


    public String getFormula() {
        return formula;
    }

    public void setFormula(String formula) {
        this.formula = formula;
    }

    private String formula;

    private boolean isSelected = false;

    private JCheckBox checkBox;
    public CustomFormulaDisplay(String string){
        super();
        this.setLayout(new BorderLayout());
        checkBox = new JCheckBox();
        this.add(checkBox, BorderLayout.WEST);

        JTextArea text = new JTextArea(2, 1);
        text.setEditable(false);
        text.setText(string);

       // JLabel text = new JLabel("Test");
        this.add(text, BorderLayout.CENTER);
        this.setVisible(true);

    }



}
