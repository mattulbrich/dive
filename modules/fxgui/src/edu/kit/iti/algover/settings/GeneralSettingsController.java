package edu.kit.iti.algover.settings;

import com.jfoenix.controls.JFXComboBox;
import com.jfoenix.controls.JFXTextField;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.control.TextField;
import javafx.scene.layout.AnchorPane;

import java.io.IOException;

public class GeneralSettingsController implements ISettingsController {

    @FXML
    private TextField currentFontSizeEditor;

    @FXML
    private TextField currentFontSizeSeqView;

    @FXML
    private TextField getCurrentFontSizeScriptEditor;


    private Node settingsPanel;

    private static final String settingsFile = "GeneralSettings.properties";

    private static final String name = "General";



    public GeneralSettingsController(){
        FXMLLoader loader = new FXMLLoader(getClass().getResource("GeneralTab.fxml"));
        loader.setController(this);
        try {
            settingsPanel = loader.load();
        } catch (IOException e) {
            settingsPanel = new Label(e.getMessage());
        }
        settingsPanel.setUserData(name);
        addFontSizes();


    }

    private void addFontSizes() {

    }

    @Override
    public Node getNode() {
        return settingsPanel;
    }

    @Override
    public void save() {
        //TODO
        //in den Home ordner

    }

    @Override
    public String getName() {
        return name;
    }
}
