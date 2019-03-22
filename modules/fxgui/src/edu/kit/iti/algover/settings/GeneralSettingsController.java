package edu.kit.iti.algover.settings;

import javafx.fxml.FXMLLoader;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.layout.AnchorPane;

import java.io.IOException;

public class GeneralSettingsController implements SettingsSupplier {

    private Node settingsPanel;

    private static final String settingsFile = "generalSettings.properties";



    public GeneralSettingsController(){
        FXMLLoader loader = new FXMLLoader(getClass().getResource("GeneralTab.fxml"));
        loader.setController(this);
        try {
            settingsPanel = loader.load();
        } catch (IOException e) {
            settingsPanel = new Label(e.getMessage());
        }
        settingsPanel.setUserData("General");

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
}
