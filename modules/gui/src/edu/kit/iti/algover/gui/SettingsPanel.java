package edu.kit.iti.algover.gui;

import net.miginfocom.swing.MigLayout;

import javax.swing.*;

/**
 * Created by Azadeh Shirvanian on 21.11.2016.
 */
public abstract class SettingsPanel extends JPanel {

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

    public SettingsPanel (GUICenter center){

        this.center = center;
        createPanel();
    }

    public JSpinner getTimeoutSpinner() {
        return timeoutSpinner;
    }

    public JTextField getPathText() {
        return pathText;
    }

    public void createPanel(){

      //  this.setBorder(BorderFactory.createTitledBorder(BorderFactory.createEtchedBorder(),"Settings for Dafny"));

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

       // browseButton.setAction(new SettingsDafnyBrowseAction(center));
    }
}
