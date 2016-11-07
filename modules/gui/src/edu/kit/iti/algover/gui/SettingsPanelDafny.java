package edu.kit.iti.algover.gui;

import net.miginfocom.swing.MigLayout;

import javax.swing.*;

/**
 * Created by Azadeh Shirvanian on 04.10.2016.
 */
public class SettingsPanelDafny extends JPanel {

    GUICenter center;

    JLabel timeoutLabel;
    JLabel pathLabel;
    JTextField pathText;
    JButton browseButton;
    JSpinner timeoutSpinner;
    SpinnerNumberModel spinnerModel;

    int start = 100;
    int min = 0;
    int max = 1000;
    int step = 5;

    public SettingsPanelDafny(GUICenter center){

        this.center = center;
        createDafnyPanel();
    }

    public JSpinner getTimeoutSpinner() {
        return timeoutSpinner;
    }

    public void createDafnyPanel(){

        this.setBorder(BorderFactory.createTitledBorder(BorderFactory.createEtchedBorder(),"Settings for Dafny"));

        timeoutLabel = new JLabel("Timeout [ms]:");
        spinnerModel = new SpinnerNumberModel(start, min, max, step);
        timeoutSpinner = new JSpinner(spinnerModel);
        pathLabel = new JLabel("Path to executable:");
        pathText = new JTextField(50);
        browseButton = new JButton("...");

        MigLayout mig = new MigLayout(
                "",       //Layout constraints
                "[][][]",               // Column constraints
                "[][]"          // Row constraints
        );

        this.setLayout(mig);

        this.add(timeoutLabel);
        this.add(timeoutSpinner, "wrap");
        this.add(pathLabel);
        this.add(pathText);
        this.add(browseButton, "wrap");
    }
}
