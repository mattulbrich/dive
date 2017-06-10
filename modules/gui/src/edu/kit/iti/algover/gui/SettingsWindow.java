/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.gui;

//import edu.kit.iti.algover.Actions.SettingsSelectionListener;

import edu.kit.iti.algover.Actions.SettingsCancelButtonAction;
import net.miginfocom.swing.MigLayout;

import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

/**
 * Created by Azadeh Shirvanian on 27.09.2016.
 */
public class SettingsWindow extends JDialog implements ActionListener {

    GUICenter center;
    DefaultListModel<String> listModel = new DefaultListModel<>();
    JList settingsList;
    JPanel buttonPanel;
    JPanel cards;
    JButton okButton;
    JButton applyButton;
    JButton cancelButton;

    private SettingsPanelGeneral settingsPanelGeneral;
    private SettingsPanel settingsPanel;

    // To save the settings information:

    List<Integer> timeoutList = new ArrayList<>();
    JSpinner z3TimeoutSpinner;
    JSpinner dafnyTimeoutSpinner;
    JSpinner keyTimeoutSpinner;
    SettingsPanelZ3 settingsPanelZ3;
    SettingsPanelDafny settingsPanelDafny;
    SettingsPanelKeY settingsPanelKeY;
    List<String> pathList = new ArrayList<>();
    JTextField generalPathTextField;
    JTextField z3PathTextField;
    JTextField dafnyPathTextField;
    JTextField keyPathTextField;



    Component settingsMainPanel;


    public SettingsWindow(GUICenter center) {

        super(center.getMainwindow());
        this.center = center;
        center.getMainwindow().setSettingsWindow(this);
        createSettingsWindow();
    }

    public void createSettingsWindow() {

        okButton = new JButton("OK");
        applyButton = new JButton("Apply");
        cancelButton = new JButton("Cancel");

        this.setLayout(new BorderLayout());
        this.setDefaultCloseOperation(JDialog.DISPOSE_ON_CLOSE);
        this.setTitle("Prover Settings");
        this.setSize(600, 200);
        //  this.setModal(true);

        //list on the left

        listModel.addElement("General");
        listModel.addElement("Z3");
        listModel.addElement("Dafny");
        listModel.addElement("KeY");
        settingsList = new JList(listModel);
        settingsList.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
        settingsList.setSelectedIndex(0);
        settingsList.setBorder(BorderFactory.createEmptyBorder(5, 6, 5, 13));

        this.add(new JScrollPane(settingsList), BorderLayout.WEST);

        // button panel

        MigLayout mig = new MigLayout(
                "",       //Layout constraints
                "[grow][][][]",               // Column constraints
                "[]"          // Row constraints
        );

        buttonPanel = new JPanel(mig);

        buttonPanel.add(cancelButton, "cell 3 0");
        buttonPanel.add(applyButton, "cell 2 0");
        buttonPanel.add(okButton, "cell 1 0");

        this.add(buttonPanel, BorderLayout.SOUTH);

        cancelButton.setAction(new SettingsCancelButtonAction(center));
        applyButton.addActionListener(this);

        //main panel (settingsPanel)

        cards = new JPanel(new CardLayout());
        cards.add(new SettingsPanelGeneral(center), "general");
        cards.add(new SettingsPanelZ3(center), "z3");
        cards.add(new SettingsPanelDafny(center), "dafny");
        cards.add(new SettingsPanelKeY(center), "key");

        //settingsMainPanel = cards.getComponent(1);
        //settingsPanelZ3 = (SettingsPanelZ3) settingsMainPanel;
        //center.setSettingsPanelZ3(settingsPanelZ3);

        this.add(cards, BorderLayout.CENTER);

        //adding default values to timeoutList
        timeoutList.add(0, 100);
        timeoutList.add(1, 100);
        timeoutList.add(2, 100);


        this.setLocationRelativeTo(null);

    }

    public void actionPerformed(ActionEvent e) {

        //if (e.getActionCommand().equals("Cancel")) {
          //  this.setVisible(false);
            //this.dispose();
          /*  System.out.println("CancelButton");

            MainWindow mw = center.getMainwindow();
            for (Window w: mw.getOwnedWindows()) {
                if(w instanceof SettingsWindow){
                    SettingsWindow sw = (SettingsWindow)w;

                }
            }
            System.out.println(mw.getOwnedWindows());


    	}*/
           /* JPanel card = null;
            for (Component comp : settingsPanel.getComponents()) {
                if (comp.getName().equals("z3")) {
                    card = (JPanel) comp;
                    SettingsPanelZ3 z3Panel = (SettingsPanelZ3) card;
                    System.out.println(z3Panel.getName2());
                }



            }*/
        //}
        if (e.getActionCommand().equals("Apply")) {

            //Storing Z3 timeout

            settingsMainPanel = cards.getComponent(1);
            settingsPanelZ3 = (SettingsPanelZ3) settingsMainPanel;
            z3TimeoutSpinner = settingsPanelZ3.getTimeoutSpinner();
            Integer z3Timeout = (Integer) z3TimeoutSpinner.getValue();
            timeoutList.remove(0);
            timeoutList.add(0, z3Timeout);

            //Storing Dafny Timeout
            settingsMainPanel = cards.getComponent(2);
            settingsPanelDafny = (SettingsPanelDafny) settingsMainPanel;
            dafnyTimeoutSpinner = settingsPanelDafny.getTimeoutSpinner();
            Integer dafnyTimeout = (Integer) dafnyTimeoutSpinner.getValue();
            timeoutList.remove(1);
            timeoutList.add(1, dafnyTimeout);

            //Storing KeY Timeout
            settingsMainPanel = cards.getComponent(3);
            settingsPanelKeY = (SettingsPanelKeY) settingsMainPanel;
            keyTimeoutSpinner = settingsPanelKeY.getTimeoutSpinner();
            Integer keyTimeout = (Integer) keyTimeoutSpinner.getValue();
            timeoutList.remove(2);
            timeoutList.add(2, keyTimeout);

            //Testing the timeoutList
            for(int i=0; i < timeoutList.size(); i++) {
                int element = timeoutList.get(i);
                System.out.println(element);
            }

            //Storing paths

            //generalPathTextField = settingsPanelGeneral.getGeneralText(); // what is panel exactly



        }
    }

    public JPanel getCards() {
        return cards;
    }

    public JList getSettingsList() {
        return settingsList;
    }

    public SettingsPanelGeneral getSettingsPanelGeneral() {
        return settingsPanelGeneral;
    }

    public void setSettingsPanelGeneral(SettingsPanelGeneral settingsPanelGeneral) {
        this.settingsPanelGeneral = settingsPanelGeneral;
    }

    public SettingsPanel getSettingsPanel() {

        //System.out.println("get SettingsPanel");
        return settingsPanel;
    }

    public void setSettingsPanel(SettingsPanel settingsPanel) {

        //System.out.println("set SettingsPanel");
        this.settingsPanel = settingsPanel;
    }
}
