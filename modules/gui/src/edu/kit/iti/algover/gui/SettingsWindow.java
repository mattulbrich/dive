package edu.kit.iti.algover.gui;

//import edu.kit.iti.algover.Actions.SettingsSelectionListener;
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
    JPanel cards;
    JPanel buttonPanel;
    JButton okButton;
    JButton applyButton;
    JButton cancelButton;


    public SettingsWindow (GUICenter center)
    {
        this.center = center;
        createSettingsWindow();
    }

    public JPanel getCards() {
        return cards;
    }

    public JList getSettingsList() {
        return settingsList;
    }

    public void createSettingsWindow(){

        okButton = new JButton("OK");
        applyButton = new JButton("Apply");
        cancelButton = new JButton("Cancel");

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


        //main panel (cards)

        cards = new JPanel(new CardLayout());
        cards.add(new SettingsPanelGeneral(center), "general");
        cards.add(new SettingsPanelZ3(center), "z3");
        cards.add(new SettingsPanelDafny(center), "dafny");
        cards.add(new SettingsPanelKeY(center), "key");

        this.add(cards, BorderLayout.CENTER);


        this.setLocationRelativeTo(null);

    }

}
