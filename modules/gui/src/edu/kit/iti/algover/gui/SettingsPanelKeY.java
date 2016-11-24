package edu.kit.iti.algover.gui;

import edu.kit.iti.algover.Actions.SettingsKeYBrowseAction;
import net.miginfocom.swing.MigLayout;

import javax.swing.*;

/**
 * Created by Azadeh Shirvanian on 04.10.2016.
 */
public class SettingsPanelKeY extends SettingsPanel {


    public SettingsPanelKeY(GUICenter center){

        super(center);
        //this.center = center;
        //center.setSettingsPanelKeY(this);
        this.setBorder(BorderFactory.createTitledBorder(BorderFactory.createEtchedBorder(),"Settings for KeY"));
    }

}
