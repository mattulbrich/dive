package edu.kit.iti.algover.Actions;

import edu.kit.iti.algover.gui.GUICenter;
import edu.kit.iti.algover.gui.SettingsPanelZ3;
import edu.kit.iti.algover.gui.SettingsWindow;

import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;
import java.io.File;

/**
 * Created by Azadeh Shirvanian on 04.11.2016.
 */
public class SettingsZ3BrowseAction extends AbstractAction {

    GUICenter c;
    SettingsWindow settingsWindow;
    SettingsPanelZ3 settingsPanelZ3;
    JTextField pathTextField;

    public SettingsZ3BrowseAction(GUICenter center){

        this.c = center;
        settingsWindow = c.getMainwindow().getSettingsWindow();
        settingsPanelZ3 = settingsWindow.getSettingsPanel().getSettingsPanelZ3();
        pathTextField = settingsPanelZ3.getPathText();

        if (settingsWindow == null)
            System.out.println("Window is null");

        if (settingsPanelZ3 == null)
            System.out.println("Panel is null");

        this.putValue(AbstractAction.NAME, "...");
        //this.putValue(AbstractAction.ACCELERATOR_KEY, KeyStroke.getKeyStroke(KeyEvent.VK_O, KeyEvent.CTRL_MASK));
        //this.putValue(AbstractAction.MNEMONIC_KEY, KeyEvent.VK_O);
    }

    @Override
    public void actionPerformed(ActionEvent e) {

        JFileChooser fc = new JFileChooser();
        fc.setDialogTitle("Browse for File");
        int result = fc.showDialog(settingsWindow, "OK");
        if (result == JFileChooser.APPROVE_OPTION) {
            File selectedFile = fc.getSelectedFile();
            pathTextField.setText(selectedFile.getAbsolutePath());
        }

    }
}
