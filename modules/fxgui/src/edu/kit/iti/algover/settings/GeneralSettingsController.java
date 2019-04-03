package edu.kit.iti.algover.settings;

import com.jfoenix.controls.JFXComboBox;
import com.jfoenix.controls.JFXTextField;
import edu.kit.iti.algover.MainController;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.control.TextField;
import javafx.scene.layout.AnchorPane;

import java.io.IOException;
import java.util.prefs.Preferences;

public class GeneralSettingsController implements ISettingsController {

    @FXML
    private TextField currentFontSizeEditor;

    @FXML
    private TextField currentFontSizeSeqView;

    @FXML
    private TextField getCurrentFontSizeScriptEditor;


    private Node settingsPanel;
//TODO woanders hin
    private Preferences preferences;

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
        preferences = MainController.systemprefs;
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
        preferences.put("FONT_SIZE_EDITOR", currentFontSizeEditor.getText());

      //  preferences.put("FONT_SIZE_SEQ_VIEW", currentFontSizeSeqView.getText());
      //  preferences.put("FONT_SIZE_SCRIPT_EDITOR", getCurrentFontSizeScriptEditor.getText());
        //TODO
        //in den Home ordner

    }

    @Override
    public String getName() {
        return name;
    }
}
