package edu.kit.iti.algover.settings;

import com.jfoenix.controls.JFXButton;
import com.jfoenix.controls.JFXListView;
import com.sun.javafx.collections.ObservableListWrapper;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.project.Configuration;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.project.XMLProjectManager;
import edu.kit.iti.algover.util.Pair;
import javafx.beans.property.SimpleObjectProperty;
import javafx.collections.ObservableList;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Node;
import javafx.scene.control.*;
import javafx.scene.control.cell.TextFieldListCell;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Region;
import javafx.scene.layout.VBox;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.*;
import java.util.function.Supplier;
import java.util.logging.Logger;
import java.util.stream.Collectors;

import edu.kit.iti.algover.settings.ProjectSettings;
import edu.kit.iti.algover.settings.ProjectSettings.Property;
import edu.kit.iti.algover.util.FormatException;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.StringValidators.OptionStringValidator;
import edu.kit.iti.algover.util.Util;
import javafx.util.StringConverter;


public class ProjectSettingsController implements SettingsSupplier {

    public static final String NAME = "Project";

    private Node settingsPanel;

    @FXML
    private VBox container;

    @FXML
    private VBox projectConfigSettings;

    @FXML
    private TextField projectName;

    @FXML
    private JFXListView<File> dafnyFiles;

    @FXML
    private JFXListView<File> libFiles;

    @FXML
    private JFXButton addDafnyFilesButton;

    @FXML
    private JFXButton delDafnyFilesButton;

    @FXML
    private JFXButton addLibFilesButton;

    @FXML
    private JFXButton delLibFilesButton;


    public Configuration getConfig() {
        return config.get();
    }

    public SimpleObjectProperty<Configuration> configProperty() {
        return config;
    }

    public void setConfig(Configuration config) {
        this.config.set(config);
    }

    private SimpleObjectProperty<Configuration> config = new SimpleObjectProperty<>(new Configuration(), "Configuration");

    public ProjectManager getManager() {
        return manager.get();
    }

    public SimpleObjectProperty<ProjectManager> managerProperty() {
        return manager;
    }

    public void setManager(ProjectManager manager) {
        this.manager.set(manager);
    }

    private SimpleObjectProperty<ProjectManager> manager = new SimpleObjectProperty<>(null, "Configuration");


    public ProjectSettingsController() {
        setConfig(new Configuration());
        FXMLLoader loader = new FXMLLoader(getClass().getResource("ProjectSettingsView.fxml"));
        loader.setController(this);
        try {
            settingsPanel = loader.load();
        } catch (IOException e) {
            settingsPanel = new Label(e.getMessage());
        }
        settingsPanel.setUserData(NAME);
        createSettingsFields();
        addAllEventHandler();
        addCellFactories();
        
        config.addListener((observable, oldValue, newValue) -> {
            if(newValue != null) {
                addProjectContents();
            }
        });
        managerProperty().addListener((observable, oldValue, newValue) -> {
            addProjectContents();
        });

    }

    private void addProjectContents() {
        Project p = manager.get().getProject();
        File baseDir = p.getBaseDir();
        this.projectName.setText(baseDir.toString());

        //add Dafnyfiles
        List<DafnyFile> allDafnyFiles = p.getDafnyFiles();
        List<DafnyFile> libs = allDafnyFiles.stream().filter(dafnyFile -> dafnyFile.isInLibrary()).collect(Collectors.toList());
        List<DafnyFile> otherDafnyFiles = allDafnyFiles.stream().filter(dafnyFile -> !dafnyFile.isInLibrary()).collect(Collectors.toList());

        List<File> collectDfyFiles = otherDafnyFiles.stream().map(dafnyFile -> {
            try {
                return dafnyFileToFile(dafnyFile);
            } catch (FileNotFoundException e) {
                e.printStackTrace();
                return null;
            }
        }).collect(Collectors.toList());

        this.dafnyFiles.getItems().addAll(collectDfyFiles);

        List<File> collectLibFiles = libs.stream().map(dafnyFile -> {
            try {
                return dafnyFileToFile(dafnyFile);
            } catch (FileNotFoundException e) {
                e.printStackTrace();
                return null;
            }
        }).collect(Collectors.toList());

        this.libFiles.getItems().addAll(collectDfyFiles);

        //add settings
        ProjectSettings settings = p.getSettings();

    }

    private static File dafnyFileToFile(DafnyFile df) throws FileNotFoundException {
        File f = new File(df.getFilename());
        if(f.exists()){
            return f;
        } else {
            throw new FileNotFoundException("Was not able to constrcut file "+ f.getAbsolutePath());
        }
    }
    private void addCellFactories(){
        dafnyFiles.setCellFactory(param ->
                {
                    TextFieldListCell<File> txt = new TextFieldListCell<>();
                    txt.setConverter(new FileStringConverter());
                    return txt;
                });

        libFiles.setCellFactory(param ->
        {
            TextFieldListCell<File> txt = new TextFieldListCell<>();
            txt.setConverter(new FileStringConverter());
            return txt;
        });

    }
    private void addAllEventHandler() {

    }

    private void createSettingsFields() {
        System.out.println("getConfig() = " + getConfig());
        Map<String, String> settings = getConfig().getSettings();
        if(settings == null) {
            settings = Collections.emptyMap();
        }

        List<Pair<Supplier<String>, Property>> validators = new ArrayList<>();
        for (Property property : ProjectSettings.getDefinedProperties()) {
            projectConfigSettings.getChildren().add(new Label(property.key));

            if(property.validator instanceof OptionStringValidator) {
                OptionStringValidator validator = (OptionStringValidator) property.validator;
                Collection<? extends CharSequence> options = validator.getOptions();
                ObservableList<String> olist =
                        new ObservableListWrapper<>(Util.map(options, Object::toString));
                String value = settings.get(property.key);
                ChoiceBox<String> choiceBox = new ChoiceBox<>(olist);
                if(value != null) {
                    choiceBox.setValue(value);
                }
                projectConfigSettings.getChildren().add(choiceBox);
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
                projectConfigSettings.getChildren().add(textField);
                validators.add(new Pair<>(() -> textField.getText(), property));
            }
        }

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


    private static class FileStringConverter extends StringConverter<File> {
        @Override
        public String toString(File object) {
            return object.getName().toString();
        }

        @Override
        public File fromString(String string) {
            return new File(string);
        }
    }
}


