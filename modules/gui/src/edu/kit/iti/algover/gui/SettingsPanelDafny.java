package edu.kit.iti.algover.gui;

import edu.kit.iti.algover.Actions.SettingsDafnyBrowseAction;
import edu.kit.iti.algover.Actions.SettingsZ3BrowseAction;
import net.miginfocom.swing.MigLayout;

import javax.swing.*;

/**
 * Created by Azadeh Shirvanian on 04.10.2016.
 */
public class SettingsPanelDafny extends SettingsPanel {

    public SettingsPanelDafny(GUICenter center){

        super(center);
        setSettingsPanelDafny(this);
        this.setBorder(BorderFactory.createTitledBorder(BorderFactory.createEtchedBorder(),"Settings for Dafny"));
        browseButton.setAction(new SettingsDafnyBrowseAction(center));
    }

}
