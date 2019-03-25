package edu.kit.iti.algover.settings;

import javafx.fxml.FXMLLoader;
import javafx.scene.Node;
import javafx.scene.control.Label;

import java.io.IOException;

public class ProjectSettingsController implements SettingsSupplier {

    public static final String NAME = "Project";

    private Node settingsPanel;


    public ProjectSettingsController() {
        FXMLLoader loader = new FXMLLoader(getClass().getResource("ProjectSettingsView.fxml"));
        loader.setController(this);
        try {
            settingsPanel = loader.load();
        } catch (IOException e) {
            settingsPanel = new Label(e.getMessage());
        }
        settingsPanel.setUserData(NAME);


    }

    @Override
    public Node getNode() {
        return settingsPanel;
    }

    @Override
    public void save() {
        //TODO
    }

    @Override
    public String getName() {
        return NAME;
    }


}
