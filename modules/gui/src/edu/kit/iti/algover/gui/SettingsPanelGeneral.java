package edu.kit.iti.algover.gui;

import edu.kit.iti.algover.Actions.SettingsGeneralBrowseAction;
import net.miginfocom.swing.MigLayout;

import javax.swing.*;
import java.awt.*;

/**
 * Created by Azadeh Shirvanian on 03.10.2016.
 */
public class SettingsPanelGeneral extends JPanel {

    GUICenter center;
    JLabel generalLabel;
    JTextField generalText;
    JButton generalButton;

    public SettingsPanelGeneral(GUICenter center){

        this.center = center;
        center.setSettingsPanelGeneral(this);
        createGeneralPanel();
    }

    public JTextField getGeneralText() {
        return generalText;
    }

    public void createGeneralPanel(){

        generalLabel = new JLabel("Store translation to file:");
        generalText = new JTextField(50);
        generalButton = new JButton("...");

        MigLayout mig = new MigLayout(
                "",       //Layout constraints
                "[grow][]",               // Column constraints
                "[][]"          // Row constraints
        );

        this.setLayout(mig);
        this.setBorder(BorderFactory.createEtchedBorder());

        this.add(generalLabel, "wrap");
        this.add(generalText);
        this.add(generalButton, "wrap");

        generalButton.setAction(new SettingsGeneralBrowseAction(center));
    }
}
