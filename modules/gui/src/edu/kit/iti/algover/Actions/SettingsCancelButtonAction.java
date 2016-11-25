package edu.kit.iti.algover.Actions;

import edu.kit.iti.algover.gui.GUICenter;
import edu.kit.iti.algover.gui.SettingsWindow;

import javax.swing.*;
import java.awt.event.ActionEvent;

/**
 * Created by Azadeh Shirvanian on 25.11.2016.
 */
public class SettingsCancelButtonAction extends AbstractAction {

    GUICenter c;
    SettingsWindow settingsWindow;

    public SettingsCancelButtonAction (GUICenter center){

        this.c = center;
        settingsWindow = c.getMainwindow().getSettingsWindow();

        this.putValue(AbstractAction.NAME, "Cancel");

    }


    @Override
    public void actionPerformed(ActionEvent e) {

        settingsWindow.setVisible(false);
        settingsWindow.dispose();
    }
}
