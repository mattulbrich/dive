package edu.kit.iti.algover.settings;

import javafx.beans.property.ObjectProperty;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.control.*;
import javafx.scene.control.cell.TextFieldListCell;
import javafx.scene.layout.BorderPane;
import javafx.stage.Window;
import javafx.util.StringConverter;

import java.io.IOException;
import java.util.Optional;

public class SettingsController {



    @FXML
    private ListView<Node> tabList;

    @FXML
    private DialogPane dialogPane;

    @FXML
    private Dialog<Void> dialog;

    @FXML
    private BorderPane contentContainer;


    public void setItems(ObservableList<Node> value) {
        tabList.setItems(value);
    }

    public ObservableList<Node> getItems() {
        return tabList.getItems();
    }

    public ObjectProperty<ObservableList<Node>> itemsProperty() {
        return tabList.itemsProperty();
    }

    public SettingsController(){
        FXMLLoader loader = new FXMLLoader(getClass().getResource("SettingsView.fxml"));
        loader.setController(this);

        dialog = new Dialog<>();
        dialog.setResizable(true);

        try {
            loader.load();

            createSettingsDialog();
            //close request
            Window window = dialog.getDialogPane().getScene().getWindow();
            window.setOnCloseRequest(e -> window.hide());

            tabList.getSelectionModel().getSelectedItems().addListener((ListChangeListener) o -> contentContainer.setCenter(tabList.getSelectionModel().getSelectedItem()));
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

        dialogPane.getButtonTypes().setAll(ButtonType.OK, ButtonType.CANCEL);
        dialog.setDialogPane(dialogPane);

    }



    public void showAndWait() {

        createSettingsDialog();
        Optional<Void> optional = dialog.showAndWait();
        if(optional.isPresent()){
            SettingsFactory.fireOnSave();
        }

    }


}
