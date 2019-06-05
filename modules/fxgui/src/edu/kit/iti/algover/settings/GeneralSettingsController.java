/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.settings;

import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.control.Spinner;
import javafx.scene.control.SpinnerValueFactory;

import java.io.IOException;
import java.util.prefs.BackingStoreException;
import java.util.prefs.Preferences;

public class GeneralSettingsController implements ISettingsController {

    @FXML
    private Spinner<Integer> currentFontSizeEditor;

    @FXML
    private Spinner<Integer> currentFontSizeSeqView;

    @FXML
    private Spinner<Integer> currentFontSizeScriptEditor;


    private Node settingsPanel;
//TODO woanders hin
    private Preferences preferences;

    private static final String name = "General";



    public GeneralSettingsController(Preferences systemPrefs){
        FXMLLoader loader = new FXMLLoader(getClass().getResource("GeneralTab.fxml"));
        loader.setController(this);
        try {
            settingsPanel = loader.load();
        } catch (IOException e) {
            settingsPanel = new Label(e.getMessage());
        }
        settingsPanel.setUserData(name);
        preferences = systemPrefs;

        addFontSizes();


    }

    private void addFontSizes() {
        int fontSizeEditor = preferences.getInt("FONT_SIZE_EDITOR", 12);
        int fontSizeSeqView =  preferences.getInt("FONT_SIZE_SEQ_VIEW", 12);
        int fontSizeScript = preferences.getInt("FONT_SIZE_SCRIPT_EDITOR", 12);

        currentFontSizeSeqView.setValueFactory(new SpinnerValueFactory.IntegerSpinnerValueFactory(1, 40, 12));
        currentFontSizeEditor.setValueFactory(new SpinnerValueFactory.IntegerSpinnerValueFactory(1, 40, 12));
        currentFontSizeScriptEditor.setValueFactory(new SpinnerValueFactory.IntegerSpinnerValueFactory(1, 40, 12));

        currentFontSizeEditor.getValueFactory().setValue(fontSizeEditor);
        currentFontSizeSeqView.getValueFactory().setValue(fontSizeSeqView);
        currentFontSizeScriptEditor.getValueFactory().setValue(fontSizeScript);

    }

    @Override
    public Node getNode() {
        return settingsPanel;
    }

    @Override
    public void save() {
        preferences.putInt("FONT_SIZE_EDITOR", currentFontSizeEditor.getValue());
        preferences.putInt("FONT_SIZE_SEQ_VIEW", currentFontSizeSeqView.getValue());
        preferences.putInt("FONT_SIZE_SCRIPT_EDITOR", currentFontSizeScriptEditor.getValue());

        try {
            preferences.flush();
        } catch (BackingStoreException e) {
            e.printStackTrace();
        }

    }

    @Override
    public String getName() {
        return name;
    }
}
