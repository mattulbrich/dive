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
import org.controlsfx.control.PlusMinusSlider;

import java.io.IOException;
import java.util.prefs.BackingStoreException;
import java.util.prefs.Preferences;

public class GeneralSettingsController implements ISettingsController {

    @FXML
    private TextField currentFontSizeEditor;

    //@FXML
    //private TextField currentFontSizeSeqView;

    @FXML
    private TextField currentFontSizeScriptEditor;


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
        preferences = MainController.systemprefs;
        addFontSizes();


    }

    private void addFontSizes() {
        int font_size_editor = preferences.getInt("FONT_SIZE_EDITOR", 12);
        int font_size_script = preferences.getInt("FONT_SIZE_SCRIPT", 12);
        currentFontSizeEditor.setText(Integer.toString(font_size_editor));
        currentFontSizeScriptEditor.setText(Integer.toString(font_size_script));

    }

    @Override
    public Node getNode() {
        return settingsPanel;
    }

    @Override
    public void save() {

        try {
            preferences.putInt("FONT_SIZE_EDITOR", Integer.parseInt(currentFontSizeEditor.getText()));
            preferences.putInt("FONT_SIZE_SCRIPT", Integer.parseInt(currentFontSizeScriptEditor.getText()));

            preferences.flush();

            //TODO notify components for repainting
        } catch (BackingStoreException e) {
            e.printStackTrace();
        }
        //  preferences.put("FONT_SIZE_SEQ_VIEW", currentFontSizeSeqView.getText());
        //TODO
        //in den Home ordner

    }

    @Override
    public String getName() {
        return name;
    }
}
