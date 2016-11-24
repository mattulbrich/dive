package edu.kit.iti.algover.gui;

import edu.kit.iti.algover.Actions.SettingsZ3BrowseAction;
import net.miginfocom.swing.MigLayout;

import javax.swing.*;

/**
 * Created by Azadeh Shirvanian on 04.10.2016.
 */
public class SettingsPanelZ3 extends SettingsPanel {


    public SettingsPanelZ3(GUICenter center){

        super(center);
        //this.center = center;
        //center.setSettingsPanelZ3(this);
        this.setBorder(BorderFactory.createTitledBorder(BorderFactory.createEtchedBorder(),"Settings for Z3"));
    }

}
