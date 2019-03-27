package edu.kit.iti.algover.settings;

import edu.kit.iti.algover.project.ProjectManager;
import javafx.beans.property.ObjectProperty;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Node;
import javafx.scene.control.*;
import javafx.scene.control.cell.TextFieldListCell;
import javafx.scene.layout.BorderPane;
import javafx.stage.Window;
import javafx.util.StringConverter;

import java.io.IOException;
import java.util.Optional;
import java.util.logging.Logger;

/**
 * Controller for the Settings Dialog. Loads SettingsView.fxml. Tabs supplied by ServiceLoader are laoded as well.
 */
public class SettingsController {

    @FXML
    private ListView<Node> tabList;

    @FXML
    private DialogPane dialogPane;

    @FXML
    private Dialog<ButtonType> dialog;

    @FXML
    private BorderPane contentContainer;


    private ProjectManager manager;


    public SettingsController(){
        loadSettingsViews();
    }

    private void loadSettingsViews() {
        FXMLLoader loader = new FXMLLoader(getClass().getResource("SettingsView.fxml"));
        loader.setController(this);

        dialog = new Dialog<>();
        dialog.setResizable(true);
        dialog.setWidth(600.0);
        dialog.setHeight(600.0);

        try {
            loader.load();

            createSettingsDialog();
            //close request
            Window window = dialog.getDialogPane().getScene().getWindow();
            window.setOnCloseRequest(e -> window.hide());

            tabList.getSelectionModel().getSelectedItems().addListener(new ListChangeListener<Node>() {
                @Override
                public void onChanged(Change<? extends Node> c) {
                    contentContainer.setCenter
                            (tabList.getSelectionModel().getSelectedItem());
                }
            });
            tabList.setCellFactory(param -> {
                TextFieldListCell<Node> txt = new TextFieldListCell<>();
                txt.setConverter(new StringConverter<Node>() {
                    @Override
                    public String toString(Node object) {
                        return object.getUserData().toString();
                    }

                    @Override
                    public Node fromString(String string) {
                        return null;
                    }
                });
                return txt;
            });

            } catch (IOException e) {
                e.printStackTrace();
            }
    }

    private void createSettingsDialog() {
        dialogPane.setPrefSize(600.0, 600.0);
        dialogPane.getButtonTypes().setAll(ButtonType.OK, ButtonType.CANCEL);
        dialog.setDialogPane(dialogPane);


    }


    /**
     * Show Dilaog and wait.
     */
    public void showAndWait() {
        if(manager != null){
            SettingsFactory.supplier.forEach(settingsSupplier -> {
                if(settingsSupplier.getName().equals(ProjectSettingsController.NAME)){
                    ((ProjectSettingsController) settingsSupplier).setManager(manager);
                }
            });
        }
        createSettingsDialog();
        Optional<ButtonType> optional = dialog.showAndWait();

        if(optional.isPresent() && optional.get() == ButtonType.OK){
            Logger.getGlobal().info("Saving settings");
            SettingsFactory.fireOnSave();
            Logger.getGlobal().info("Saved Settings");
        } else {
            Logger.getGlobal().info("Settings not saved");
        }

    }

    //region: getter and setter
    public void setItems(ObservableList<Node> value) {
        tabList.setItems(value);
    }

    public ObservableList<Node> getItems() {
        return tabList.getItems();
    }

    public ObjectProperty<ObservableList<Node>> itemsProperty() {
        return tabList.itemsProperty();
    }

    public ProjectManager getManager() {
        return manager;
    }

    public void setManager(ProjectManager manager) {
        this.manager = manager;
    }


}
