package edu.kit.iti.algover.Actions;

import edu.kit.iti.algover.gui.GUICenter;
import edu.kit.iti.algover.gui.MainWindow;
import edu.kit.iti.algover.gui.SettingsWindow;

import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;

/**
 * Created by Azadeh Shirvanian on 27.09.2016.
 */
public class ProverSettingsAction extends AbstractAction {

    GUICenter c;

    public ProverSettingsAction(GUICenter center){

        this.c = center;
        this.putValue(AbstractAction.NAME, "Settings...");

    }

    @Override
    public void actionPerformed(ActionEvent e) {

        SettingsWindow settingsWindow = new SettingsWindow(c);
        settingsWindow.setVisible(true);


    }
}
