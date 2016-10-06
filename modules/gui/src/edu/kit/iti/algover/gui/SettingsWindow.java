package edu.kit.iti.algover.gui;

import net.miginfocom.swing.MigLayout;

import javax.swing.*;
import javax.swing.border.Border;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;
import java.awt.*;

/**
 * Created by Azadeh Shirvanian on 27.09.2016.
 */
public class SettingsWindow extends JFrame{

    GUICenter center;
    DefaultListModel<String> listModel = new DefaultListModel<>();
    JList settingsList;
    JPanel mainPanel;
    JPanel buttonPanel;
    JButton okButton = new JButton("OK");
    JButton applyButton = new JButton("Apply");
    JButton cancelButton = new JButton("Cancel");

    public SettingsWindow (GUICenter center)
    {
        this.center = center;
        createSettingsWindow();
    }


    public void createSettingsWindow(){

        this.setLayout(new BorderLayout());
        this.setDefaultCloseOperation(JFrame.DISPOSE_ON_CLOSE);
        this.setTitle("Prover Settings");
        this.setSize(600,200);

        //list on the left

        listModel.addElement("General");
        listModel.addElement("Z3");
        listModel.addElement("Dafny");
        listModel.addElement("KeY");
        settingsList = new JList(listModel);
        settingsList.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
        settingsList.setSelectedIndex(0);
        settingsList.setBorder(BorderFactory.createEmptyBorder(5,6,5,13));

        this.add(new JScrollPane(settingsList), BorderLayout.WEST);

        // button panel

        MigLayout mig = new MigLayout(
                "",       //Layout constraints
                "[grow][][][]",               // Column constraints
                "[]"          // Row constraints
        );

        buttonPanel = new JPanel(mig);

        buttonPanel.add(cancelButton, "cell 3 0" );
        buttonPanel.add(applyButton, "cell 2 0");
        buttonPanel.add(okButton, "cell 1 0");

        this.add(buttonPanel, BorderLayout.SOUTH);


        //main panel

        mainPanel = new SettingsPanelGeneral(center);
        this.add(mainPanel, BorderLayout.CENTER);
        this.setLocationRelativeTo(null);

        settingsList.getSelectionModel().addListSelectionListener(e -> {
           // if (!e.getValueIsAdjusting()) {
                if (settingsList.getSelectedIndex() == 0)
                    mainPanel = new SettingsPanelGeneral(center);
                else if (settingsList.getSelectedIndex() == 1)
                    mainPanel = new SettingsPanelZ3(center);
                else if (settingsList.getSelectedIndex() == 2)
                    mainPanel = new SettingsPanelDafny(center);
                else if (settingsList.getSelectedIndex() == 3)
                    mainPanel = new SettingsPanelKeY(center);
                this.add(mainPanel, BorderLayout.CENTER);
            //}
        });


    }
}
