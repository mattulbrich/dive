package edu.kit.iti.algover.gui;

import edu.kit.iti.algover.Actions.SettingsZ3BrowseAction;
import net.miginfocom.swing.MigLayout;

import javax.swing.*;

/**
 * Created by Azadeh Shirvanian on 04.10.2016.
 */
public class SettingsPanelZ3 extends JPanel {

    GUICenter center;

    JLabel timeoutLabel;
    JLabel pathLabel;
    JTextField pathText;
    JButton browseButton;
    JSpinner timeoutSpinner;
    SpinnerNumberModel spinnerModel;

//    String name = "Name:z3";
    int start = 100;
    int min = 0;
    int max = 1000;
    int step = 5;

    public SettingsPanelZ3(GUICenter center){

        this.center = center;
        center.setSettingsPanelZ3(this);
        createZ3Panel();
    }

/*    public String getName2() {
        return name;
    }*/

    public JSpinner getTimeoutSpinner(){
        return this.timeoutSpinner;
    }

    public JTextField getPathText() {
        return pathText;
    }

    public void createZ3Panel(){

        this.setBorder(BorderFactory.createTitledBorder(BorderFactory.createEtchedBorder(),"Settings for Z3"));

        timeoutLabel = new JLabel("Timeout [ms]:");
        spinnerModel = new SpinnerNumberModel(start, min, max, step);
        timeoutSpinner = new JSpinner(spinnerModel);
        pathLabel = new JLabel("Path to executable:");
        pathText = new JTextField(50);
       // pathText.setText("Path");
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

        browseButton.setAction(new SettingsZ3BrowseAction(center));
    }
}
