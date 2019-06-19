/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.project;

import edu.kit.iti.algover.settings.ProjectSettings;
import edu.kit.iti.algover.settings.ProjectSettings.Property;
import edu.kit.iti.algover.util.FormatException;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.StringValidators.OptionStringValidator;
import edu.kit.iti.algover.util.Util;
import javafx.application.Platform;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.event.ActionEvent;
import javafx.geometry.Insets;
import javafx.scene.control.Alert;
import javafx.scene.control.Alert.AlertType;
import javafx.scene.control.Button;
import javafx.scene.control.ButtonType;
import javafx.scene.control.ChoiceBox;
import javafx.scene.control.Dialog;
import javafx.scene.control.Label;
import javafx.scene.control.ScrollPane;
import javafx.scene.control.TextArea;
import javafx.scene.control.TextField;
import javafx.scene.control.Tooltip;
import javafx.scene.layout.GridPane;
import org.xml.sax.SAXException;

import javax.xml.bind.JAXBException;
import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Supplier;


// look at http://code.makery.ch/blog/javafx-dialogs-official/


public class ConfigurationDialog {

    public static Optional<Configuration> showConfigurationDialog(Configuration config) {
        // Create the custom dialog.
        Dialog<Configuration> dialog = new Dialog<>();
        dialog.setTitle("Project Configuration");
        dialog.setHeaderText("Edit Project Configuration");

        // Set the icon (must be included in the project).
        // dialog.setGraphic(new ImageView(this.getClass().getResource("login.png").toString()));

        // Set the button types.
        dialog.getDialogPane().getButtonTypes().addAll(ButtonType.OK, ButtonType.CANCEL);

        // Create the username and password labels and fields.
        GridPane grid = new GridPane();
        grid.setHgap(10);
        grid.setVgap(10);

        grid.setPadding(new Insets(20, 10, 10, 10));

        TextField projectName = new TextField();
        projectName.setPromptText("Name of the project");

        TextArea dafnyFiles = new TextArea();
        dafnyFiles.setPromptText("List input files on separate lines");
        if(config.getDafnyFiles() != null) {
            dafnyFiles.setText(Util.join(config.getDafnyFiles(), "\n"));
        }

        TextArea libFiles = new TextArea();
        libFiles.setPromptText("List lib files on separate lines");
        if(config.getLibFiles() != null) {
            libFiles.setText(Util.join(config.getLibFiles(), "\n"));
        }

        int row = 0;
        grid.add(new Label("Name of the project"), 0, row++);
        grid.add(projectName, 0, row++);
        grid.add(new Label("Dafny input files"), 0, row++);
        grid.add(dafnyFiles, 0, row++);
        grid.add(new Label("Dafny libs"), 0, row++);
        grid.add(libFiles, 0, row++);

        Map<String, String> settings = config.getSettings();
        if(settings == null) {
            settings = Collections.emptyMap();
        }

        List<Pair<Supplier<String>, Property>> validators = new ArrayList<>();
        for (Property property : ProjectSettings.getDefinedProperties()) {
            grid.add(new Label(property.key), 0, row++);

            if(property.validator instanceof OptionStringValidator) {
                OptionStringValidator validator = (OptionStringValidator) property.validator;
                Collection<? extends CharSequence> options = validator.getOptions();
                ObservableList<String> olist =
                        FXCollections.observableList(Util.map(options, x -> x.toString()));
                String value = settings.get(property.key);
                ChoiceBox<String> choiceBox = new ChoiceBox<>(olist);
                if(value != null) {
                    choiceBox.setValue(value);
                }
                grid.add(choiceBox, 0, row++);
                validators.add(new Pair<>(() -> choiceBox.getValue(), property));
            } else {
                TextField textField = new TextField();
                String value = settings.get(property.key);
                if(value != null) {
                    textField.setText(value);
                }
                textField.textProperty().addListener((observable, oldValue, newValue) -> {
                    try{
                        if(property.validator != null && !newValue.isEmpty()) {
                            property.validator.validate(newValue);
                        }
                        textField.setTooltip(null);
                        textField.setStyle(null);
                    } catch(FormatException ex) {
                        textField.setTooltip(new Tooltip(ex.getMessage()));
                        textField.setStyle("-fx-background-color:red;");
                    }
                });
                grid.add(textField, 0, row++);
                validators.add(new Pair<>(() -> textField.getText(), property));
            }
        }

        ScrollPane scroll = new ScrollPane(grid);
        scroll.setPrefViewportHeight(500.);

        dialog.getDialogPane().setContent(scroll);

        // Request focus on the username field by default.
        // Platform.runLater(() -> username.requestFocus());

        final Button cancel = (Button) dialog.getDialogPane().lookupButton(ButtonType.OK);
        cancel.addEventFilter(ActionEvent.ACTION, ev -> {
                    for (Pair<Supplier<String>, Property> validator : validators) {
                        try {
                            String text = validator.fst.get();
                            if(!text.isEmpty())
                                validator.snd.validator.validate(text);
                        } catch (FormatException ex) {
                            ev.consume();
                            Alert alert = new Alert(AlertType.ERROR);
                            alert.setTitle("Illegal data");
                            alert.setHeaderText("Field '" + validator.snd.key +
                                            "' contains illegal input");
                            alert.setContentText(ex.getMessage());
                            alert.showAndWait();
                            return;
                        }
                    }
                }
        );


        // Convert the result to a username-password-pair when the login button is clicked.
        dialog.setResultConverter(dialogButton -> {
            Configuration result = new Configuration();
            result.setDafnyFiles(fromTextArea(dafnyFiles));
            result.setLibFiles(fromTextArea(libFiles));

            Map<String, String> props = new HashMap<>();
            for (Pair<Supplier<String>, Property> value : validators) {
                String v = value.fst.get();
                if(!v.trim().isEmpty()) {
                    props.put(value.snd.key, v);
                }
            }

            result.setSettings(props);

            return result;
        });
        dialog.setResizable(true);
        dialog.onShownProperty().addListener(e -> {
            Platform.runLater(() -> dialog.setResizable(false));
        });

        Optional<Configuration> result = dialog.showAndWait();
        return result;
    }

    private static List<File> fromTextArea(TextArea dafnyFiles) {
        String text = dafnyFiles.getText().trim();
        if(text.isEmpty()) {
            return Collections.emptyList();
        }

        List<String> names = Util.readOnlyArrayList(text.split(" *\n *"));
        List<File> files = Util.map(names, x -> new File(x));
        return files;
    }

    public static void main(String[] args) throws JAXBException, SAXException {

        Configuration config;
        if(args.length == 0) {
            config = new Configuration();
        } else {
            config = ConfigXMLLoader.loadConfigFile(new File(args[0]));
        }

        com.sun.javafx.application.PlatformImpl.startup(()->{});
        Platform.runLater(() -> showConfigurationDialog(config)
                .ifPresent(c -> System.out.println(exportConfiguration(c))));
    }

    private static String exportConfiguration(Configuration config) {
        try {
            return ConfigXMLLoader.toString(config);
        } catch (JAXBException e) {
            e.printStackTrace();
            return "????";
        }
    }

}