package edu.kit.iti.algover.Actions;

import edu.kit.iti.algover.gui.GUICenter;
import edu.kit.iti.algover.gui.SettingsPanelDafny;
import edu.kit.iti.algover.gui.SettingsWindow;

import javax.swing.*;
import java.awt.event.ActionEvent;
import java.io.File;

/**
 * Created by Azadeh Shirvanian on 09.11.2016.
 */
public class SettingsDafnyBrowseAction extends AbstractAction {

    GUICenter c;
    SettingsWindow settingsWindow;
    SettingsPanelDafny settingsPanelDafny;
    JTextField pathTextField;

    public SettingsDafnyBrowseAction(GUICenter center){

        this.c = center;
        settingsWindow = c.getMainwindow().getSettingsWindow();
        settingsPanelDafny = settingsWindow.getSettingsPanel().getSettingsPanelDafny();
        pathTextField = settingsPanelDafny.getPathText();

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

