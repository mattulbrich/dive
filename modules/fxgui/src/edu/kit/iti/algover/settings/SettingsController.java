/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.settings;

import edu.kit.iti.algover.MainController;
import edu.kit.iti.algover.project.ProjectManager;
import javafx.beans.property.ObjectProperty;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.geometry.Insets;
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
    private ListView<ISettingsController> tabList;

    @FXML
    private DialogPane dialogPane;

    @FXML
    private Dialog<ButtonType> dialog;

    @FXML
    private BorderPane contentContainer;

    private double height;

    private double width;

    private ProjectManager manager;

    private MainController mainController;

    public SettingsController(MainController mainController, double height, double width){
        this.mainController = mainController;
        this.height = height;
        this.width = width;
        loadSettingsViews();
    }


    private void loadSettingsViews() {
        FXMLLoader loader = new FXMLLoader(getClass().getResource("SettingsView.fxml"));
        loader.setController(this);

        dialog = new Dialog<>();
        dialog.setResizable(true);
        //dialog.setWidth(width/2);
        //dialog.setHeight(height);

        try {
            loader.load();

            createSettingsDialog();
            //close request
            Window window = dialog.getDialogPane().getScene().getWindow();
            window.setOnCloseRequest(e -> window.hide());

            tabList.getSelectionModel().getSelectedItems().addListener(new ListChangeListener<ISettingsController>() {
                @Override
                public void onChanged(Change<? extends ISettingsController> c) {
                    Node node = tabList.getSelectionModel().getSelectedItem().getNode();
                    ScrollPane sp = new ScrollPane(node);
                    sp.setFitToWidth(true);
                    contentContainer.setCenter(sp);
                }
            });
            tabList.setCellFactory(param -> {
                TextFieldListCell<ISettingsController> txt = new TextFieldListCell<>();
                txt.setConverter(new StringConverter<ISettingsController>() {
                    @Override
                    public String toString(ISettingsController object) {
                        return object.getName();
                    }

                    @Override
                    public ISettingsController fromString(String string) {
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
       // dialogPane.setPrefSize(600.0, 600.0);
        dialogPane.setPadding(new Insets(20,20,20,20));
        dialogPane.getButtonTypes().setAll(ButtonType.OK, ButtonType.CANCEL);

        dialogPane.setPrefHeight(height*0.8);
        dialogPane.setMinWidth(width*0.5);
        dialog.setDialogPane(dialogPane);



    }


    /**
     * Show Dialog and wait.
     */
    public void showAndWait() {
        createSettingsDialog();
        tabList.getSelectionModel().selectFirst();
        Optional<ButtonType> optional = dialog.showAndWait();

        if(optional.isPresent() && optional.get() == ButtonType.OK){
            Logger.getGlobal().info("Saving settings");
            for (ISettingsController iSettingsController : getItems()) {
                try {
                    iSettingsController.save();
                } catch (IOException e) {
                    e.printStackTrace();
                }
            }
            Logger.getGlobal().info("Saved Settings");
            mainController.reloadWholeGUIcontents();

        } else {
            Logger.getGlobal().info("Settings not saved");
        }

    }

    //region: getter and setter
    public void setItems(ObservableList<ISettingsController> value) {
        tabList.setItems(value);
    }

    public ObservableList<ISettingsController> getItems() {
        return tabList.getItems();
    }

    public ObjectProperty<ObservableList<ISettingsController>> itemsProperty() {
        return tabList.itemsProperty();
    }

    public ProjectManager getManager() {
        return manager;
    }

    public void setManager(ProjectManager manager) {
        this.manager = manager;
    }


}
