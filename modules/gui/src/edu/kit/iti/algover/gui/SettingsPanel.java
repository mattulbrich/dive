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

    private SettingsPanelZ3 settingsPanelZ3;
    private SettingsPanelDafny settingsPanelDafny;
    private SettingsPanelKeY settingsPanelKeY;

    int start = 100;
    int min = 0;
    int max = 1000;
    int step = 5;

    public SettingsPanel (GUICenter center){

        this.center = center;
        createPanel();
    }

    public void createPanel(){

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

    public JSpinner getTimeoutSpinner() {
        return timeoutSpinner;
    }

    public JTextField getPathText() {
        return pathText;
    }

    public SettingsPanelZ3 getSettingsPanelZ3() {
        return settingsPanelZ3;
    }

    public void setSettingsPanelZ3(SettingsPanelZ3 settingsPanelZ3) {
        this.settingsPanelZ3 = settingsPanelZ3;
    }

    public SettingsPanelDafny getSettingsPanelDafny() {
        return settingsPanelDafny;
    }

    public void setSettingsPanelDafny(SettingsPanelDafny settingsPanelDafny) {
        this.settingsPanelDafny = settingsPanelDafny;
    }

    public SettingsPanelKeY getSettingsPanelKeY() {
        return settingsPanelKeY;
    }

    public void setSettingsPanelKeY(SettingsPanelKeY settingsPanelKeY) {
        this.settingsPanelKeY = settingsPanelKeY;
    }
}
