/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.settings;

import com.jfoenix.controls.JFXListView;
import com.jfoenix.controls.JFXRadioButton;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.project.*;
import edu.kit.iti.algover.util.*;
import javafx.application.Platform;
import javafx.beans.property.SimpleBooleanProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Node;
import javafx.scene.control.*;
import javafx.scene.control.cell.TextFieldListCell;
import javafx.scene.layout.VBox;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.function.Supplier;
import java.util.logging.Logger;

import edu.kit.iti.algover.settings.ProjectSettings.Property;
import edu.kit.iti.algover.util.StringValidators.OptionStringValidator;
import javafx.stage.DirectoryChooser;
import javafx.stage.FileChooser;
import javafx.util.StringConverter;
import org.controlsfx.validation.ValidationResult;
import org.controlsfx.validation.ValidationSupport;

import javax.xml.bind.JAXBException;

/**
 * Controller for the Project Settings View
 * @author S.Grebing
 */
public class ProjectSettingsController implements ISettingsController {

    public static final String NAME = "Project";

    private Node settingsPanel;

    @FXML
    private VBox projectConfigSettings;

    @FXML
    private TextField projectPath;

    @FXML
    private TextField configFileName;

    @FXML
    private TextField masterFileName;

    @FXML
    private JFXListView<File> dafnyFiles;

    @FXML
    private JFXListView<File> libFiles;

    @FXML
    private Button addDafnyFilesButton;

    @FXML
    private Button delDafnyFilesButton;

    @FXML
    private Button addLibFilesButton;

    @FXML
    private Button delLibFilesButton;

    @FXML
    private CheckBox saveOption;

    @FXML
    private Button fileChooserButton;

    @FXML
    private Button newDafnyFileButton;

    @FXML
    private JFXRadioButton xmlFormat;

    @FXML
    private JFXRadioButton dfyFormat;



    private ToggleGroup formatButtonsGroup;

    private SimpleObjectProperty<Configuration> config = new SimpleObjectProperty<>(new Configuration(), "Configuration");

    private SimpleBooleanProperty savingFormatAsXML;

    private Map<String, String> currentSettings = null;

    private List<Pair<Supplier<String>, Property>> validators;

    private ValidationSupport validationSupport = new ValidationSupport();

    private boolean saveAsXML = false;

    private ChangeListener<ProjectManager> projectManagerListener;


    /**
     * The ProjectManager for a loaded project
     */
    private SimpleObjectProperty<ProjectManager> manager = new SimpleObjectProperty<>(null, "Configuration");

    public ProjectSettingsController() {
        this(new Configuration());
    }


    public ProjectSettingsController(Configuration config){
        setConfig(config);

        FXMLLoader loader = new FXMLLoader(getClass().getResource("ProjectSettingsView.fxml"));
        loader.setController(this);

        try {
            settingsPanel = loader.load();
        } catch (IOException e) {
            e.printStackTrace();
            settingsPanel = new Label(e.getMessage());
        }
        assert settingsPanel != null;
        assert dafnyFiles != null;
        settingsPanel.setUserData(NAME);

        //ToggleGroup
        formatButtonsGroup = new ToggleGroup();
        xmlFormat.setToggleGroup(formatButtonsGroup);
        xmlFormat.setUserData("XML");
        dfyFormat.setToggleGroup(formatButtonsGroup);
        dfyFormat.setUserData("DAFNY");
        savingFormatAsXML = new SimpleBooleanProperty(saveAsXML);

        formatButtonsGroup.selectedToggleProperty().addListener(new ChangeListener<Toggle>() {
            @Override
            public void changed(ObservableValue<? extends Toggle> observable, Toggle oldValue, Toggle newValue) {
                if (newValue.isSelected()) {
                    String userData = (String) newValue.getUserData();
                    saveAsXML = userData.equals("XML");
                    savingFormatAsXML.set(saveAsXML);
                    getConfig().setSaveAsXML(saveAsXML);
                }
            }
        });
        this.masterFileName.editableProperty().bind(savingFormatAsXML.not());
        this.configFileName.editableProperty().bind(savingFormatAsXML);

     /*   Platform.runLater(() -> {
            validationSupport.registerValidator(masterFileName, this::dafnyFileExistsValidator);
    //        validationSupport.errorDecorationEnabledProperty().bind(enableValidationProperty().and(savingFormatAsXML.not()));
            validationSupport.registerValidator(configFileName, this::xmlFileExistsValidator);
        });*/

        addProjectContents();
        addCellFactories();

        this.config.addListener((observable, oldValue, newValue) -> {
            if(newValue != null) {
                addProjectContents();

            }
        });

        projectManagerListener = new ChangeListener<ProjectManager>() {
            @Override
            public void changed(ObservableValue<? extends ProjectManager> observable, ProjectManager oldValue, ProjectManager newValue) {
                if(newValue != null){
                    addProjectContents();
                    if(savingFormatAsXML.get()){
                        dfyFormat.setDisable(true);
                    } else {
                        xmlFormat.setDisable(true);
                    }
                }
            }
        };

        managerProperty().addListener(this.projectManagerListener);

        validationSupport.setErrorDecorationEnabled(false);

    }





    /**
     * Add contents to the SettingsView according to configuration
     * and disable fields if neccessary
     */
    private void addProjectContents() {
       // managerProperty().removeListener(projectManagerListener);

        Configuration configuration = configProperty().get();
        if(configuration != null) {
            if(configuration.isSaveAsXML()){
                this.configFileName.setText(configuration.getConfigFile());
                formatButtonsGroup.selectToggle(xmlFormat);
            } else{
                this.masterFileName.setText(configuration.getMasterFile().getName());
                formatButtonsGroup.selectToggle(dfyFormat);
            }
            File baseDir = configuration.getBaseDir();
            this.projectPath.setText(baseDir.toString());

            //if we have an existing project, the base directory should not be editable
            if(baseDir.exists()){
                this.projectPath.setEditable(false);
                this.projectPath.setStyle("-fx-background-color: #cdcdcd");
                this.fileChooserButton.setDisable(true);
            }


            List<File> dafnyFiles = getConfig().getDafnyFiles();
            dafnyFiles.forEach(file -> {
                if(!this.dafnyFiles.getItems().contains(file)){
                    this.dafnyFiles.getItems().add(file);
                }
            });

            List<File> libFiles = getConfig().getLibFiles();
            libFiles.forEach(file -> {
                if(!this.libFiles.getItems().contains(file)){
                    this.libFiles.getItems().add(file);
                }
            });

            //add settings
            Map<String, String> settings = getConfig().getSettings();
            HashMap<String, String> newSettings = new HashMap<>();
            for (Property property : ProjectSettings.getDefinedProperties()) {
                newSettings.put(property.key, settings.get(property.key));
            }
            currentSettings = newSettings;


        }
        createSettingsFields();
       // managerProperty().addListener(projectManagerListener);

    }

    /**
     * Add cellfactories for lists, such that we only display the short file name without path
     */
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

    /**
     * Create settings fields, possibly with input
     * @author M. Ulbrich
     */
    private void createSettingsFields() {
        if(!projectConfigSettings.getChildren().isEmpty())
            projectConfigSettings.getChildren().clear();
        if (currentSettings == null) {
            currentSettings = Collections.emptyMap();
        }
        validators = new ArrayList<>();

        for (Property property : ProjectSettings.getDefinedProperties()) {
            projectConfigSettings.getChildren().add(new Label(property.key));

            if(property.validator instanceof OptionStringValidator) {
                OptionStringValidator validator = (OptionStringValidator) property.validator;
                Collection<? extends CharSequence> options = validator.getOptions();
                ObservableList<String> olist = FXCollections.observableList(Util.map(options, x -> x.toString()));
                String value = currentSettings.get(property.key);
                ChoiceBox<String> choiceBox = new ChoiceBox<>(olist);
                if(value != null) {
                    choiceBox.setValue(value);
                } else {
                    choiceBox.setValue(property.defaultValue);
                }
                projectConfigSettings.getChildren().add(choiceBox);
                choiceBox.setTooltip(new HTMLToolTip(property.helpText));
                validators.add(new Pair<>(() -> choiceBox.getValue(), property));
            } else {
                TextField textField = new TextField();
                String value = currentSettings.get(property.key);
                if(value != null) {
                    textField.setText(value);
                } else {
                    textField.setText(property.defaultValue);
                }
                projectConfigSettings.getChildren().add(textField);
                textField.setTooltip(new Tooltip(property.helpText));
                Pair<Supplier<String>, Property> e = new Pair<>(() -> textField.getText(), property);
                Platform.runLater(() -> {
                    validationSupport.registerValidator(textField, new SettingsValidatorAdapter(e.snd.validator));
                });
                validators.add(e);

            }
        }

    }


    /**
     * Save current configuration.
     * @author M.Ulbrich
     * @modified S.Grebing
     *
     */
    @Override
    public void save() throws IOException{
        //validate
        validationSupport.setErrorDecorationEnabled(true);
        validationSupport.redecorate();
        if(validationSupport.getValidationResult().getErrors().size() > 0){
            StringBuilder errors = new StringBuilder();
            validationSupport.getValidationResult().getErrors().forEach(validationMessage -> errors.append(validationMessage.getText()));
            String text = errors.toString();
            throw new IOException(text);

        } else {
            String pathText = projectPath.getText();
            Path pPath = Paths.get(pathText);

            getConfig().setDafnyFiles(this.dafnyFiles.getItems());
            getConfig().setLibFiles(this.libFiles.getItems());

            Map<String, String> newProperties = new HashMap<>();
            for (Pair<Supplier<String>, Property> value : validators) {
                String v = value.fst.get();
                if (v != null) {
                    if (!v.trim().isEmpty()) {
                        newProperties.put(value.snd.key, v);
                    }
                } else {
                    Logger.getGlobal().severe("Saving unsuccessfull, please select " + value.getSnd().key + " and try saving again.");
                }
            }

            getConfig().setSettings(newProperties);
            File baseDir = new File(pathText);
            getConfig().setBaseDir(baseDir);

            //propagate configuration and save config
            try {
                if (saveAsXML) {
                    File filename = new File(baseDir + File.separator + this.configFileName.getText());
                    getConfig().setConfigFile(this.configFileName.getText());
                    ConfigXMLLoader.saveConfigFile(getConfig(), filename);
                    if (manager.get() != null) {
                        manager.get().updateProject(getConfig());
                    } else {
                        XMLProjectManager.saveConfiguration(getConfig());
                        manager.set(new XMLProjectManager(baseDir, this.configFileName.getText()));
                    }
                } else {
                    String masterFile = this.masterFileName.getText();
                    getConfig().setMasterFile(new File(baseDir + File.separator + masterFile));
                    if (manager.get() != null) {
                        manager.get().updateProject(getConfig());
                    } else {
                        DafnyProjectConfigurationChanger.saveConfiguration(getConfig(), getConfig().getMasterFile());
                        manager.set(new DafnyProjectManager(getConfig().getMasterFile()));
                    }
                }
                manager.get().reload(); //maybe removed?
                manager.get().getConfiguration();  //maybe removed?

            } catch (JAXBException e) {
                String msg = "Could not save configuration file";
                Logger.getGlobal().warning(msg);
                e.printStackTrace();
                ExceptionDialog ed = new ExceptionDialog(e);
                ed.setHeaderText(msg);
                ed.showAndWait();
            } catch (IOException e) {
                String msg = "Could not save project settings to file";
                Logger.getGlobal().warning(msg);
                e.printStackTrace();
                ExceptionDialog ed = new ExceptionDialog(e);
                ed.setHeaderText(msg);
                ed.showAndWait();

            } catch (FormatException | DafnyParserException | DafnyException e){
                e.printStackTrace();
                String msg = "Could not save project settings to file due to Format or parser error";
                Logger.getGlobal().warning(msg);
                ExceptionDialog ed = new ExceptionDialog(e);
                ed.setHeaderText(msg);
                ed.showAndWait();

            }
        }


    }

    @Override
    public Node getNode() {
        return settingsPanel;
    }

    @Override
    public String getName() {
        return NAME;
    }

    public ProjectManager getManager() {
        return manager.get();
    }

    public SimpleObjectProperty<ProjectManager> managerProperty() {
        return manager;
    }

    public void setManager(ProjectManager manager) {
        this.manager.set(manager);
    }

    public Configuration getConfig() {
        return config.get();
    }

    public SimpleObjectProperty<Configuration> configProperty() {
        return config;
    }

    public void setConfig(Configuration config) {
        this.config.set(config);
    }

    //region: FXML ActionHandler

    @FXML
    private void addLibFile() { addItemToList(libFiles, "Library file"); }

    @FXML
    private void removeDafnyFile() {removeSelectedFiles(dafnyFiles, dafnyFiles.getSelectionModel().getSelectedItems());
    }

    @FXML
    private void removeLibFile() { removeSelectedFiles(libFiles, libFiles.getSelectionModel().getSelectedItems());}

    @FXML
    private void addDafnyFile() {
        addItemToList(dafnyFiles, "Dafny file");
    }

    @FXML
    private void createNewDafnyFile(){
        TextInputDialog tid = new TextInputDialog();
        tid.setTitle("Name for Dafny file");
        tid.setContentText("Please enter a new filename");
        ValidationSupport dialogValid = new ValidationSupport();
        dialogValid.registerValidator(tid.getEditor(), this::dafnyFileExistsValidator);
        Optional<String> filename = tid.showAndWait();

        ValidationResult validationResult = dialogValid.getValidationResult();
        dialogValid.redecorate();
        if(validationResult.getErrors().size()<=0 && filename.isPresent()){
            File baseDir = getConfig().getBaseDir();
            try {
                Path newDfyFile= null;
                if(filename.get().endsWith(".dfy")) {
                    newDfyFile = Files.createFile(Paths.get(baseDir + File.separator + filename.get()));
                } else {
                    newDfyFile = Files.createFile(Paths.get(baseDir + File.separator + filename.get()+".dfy"));
                }
                File e = newDfyFile.toFile();
                if(!this.dafnyFiles.getItems().contains(e)){
                    this.dafnyFiles.getItems().add(e);
                }

            } catch (IOException e) {
                Logger.getGlobal().warning("Not able to create dafny file");
                e.printStackTrace();
            }

        }
       // Files.createFile(baseDir, )

    }

    @FXML
    private void openDirChooser(){
        DirectoryChooser chooser = new DirectoryChooser();

        if(getConfig().getBaseDir().equals(new File(""))){
            getConfig().setBaseDir(new File("../../doc/examples/"));
        }
        chooser.setInitialDirectory(getConfig().getBaseDir());
        File file = chooser.showDialog(this.settingsPanel.getScene().getWindow());
        getConfig().setBaseDir(file);
        this.projectPath.setText(file.getAbsolutePath());
        this.projectPath.setEditable(false);
    }


    private void addItemToList(ListView<File> list, String title){

        FileChooser chooser = new FileChooser();
        chooser.setTitle("Select a "+title);
        File initialDir;
        File newFile = new File(projectPath.getText());
        if(manager.get() != null){
            File baseDir = manager.get().getProject().getBaseDir();

            if(baseDir.equals(newFile)) {
                initialDir = baseDir;
            } else {
                initialDir = newFile;
            }
        } else {
            if(!projectPath.getText().isEmpty()) {
                initialDir = newFile;
            } else {
                initialDir = new File("doc/examples/");
            }
        }
        chooser.setInitialDirectory(initialDir);
        chooser.setSelectedExtensionFilter(new FileChooser.ExtensionFilter("Dafny Files", Collections.singletonList("dfy")));
        List<File> files = chooser.showOpenMultipleDialog(settingsPanel.getScene().getWindow());
        if(files != null){
            files.forEach(file -> {
                if (!list.getItems().contains(file)) {
                    list.getItems().add(file);
                }
            });
        }
    }

    private void removeSelectedFiles(ListView<File> list, ObservableList<File> selectedItems){
        list.getItems().removeAll(selectedItems);
    }


    //region: converter

    /**
     * Convert file entry s.t. only short file name is displayed without path information
     */
    private static class FileStringConverter extends StringConverter<File> {
        @Override
        public String toString(File file) {
            return file.getName().toString();
        }

        @Override
        public File fromString(String string) {
            return new File(string);
        }
    }



    //region: Validator


    private ValidationResult dafnyFileExistsValidator(Control c, String file) {
        if(dfyFormat.isSelected()) {
            if (!file.endsWith("dfy")) {
                return ValidationResult.fromError(c, "Please add a Dafny file with file extension \"dfy\"");
            } else {
                Path dfyFile = Paths.get(projectPath.getText()+File.separator+file);
                    if (dfyFile.toFile().exists()) {
                        return ValidationResult.fromWarning(c, "Dafny file exists and will be overwritten");
                    }
            }
        }
        return new ValidationResult();
    }

    private ValidationResult xmlFileExistsValidator(Control c, String file) {
        if (xmlFormat.isSelected()) {
            if (!file.endsWith("xml")) {
                return ValidationResult.fromError(c, "An XML file is required");
            } else {
                if (projectPath.getText().equals("")) {
                    return ValidationResult.fromError(c, "Please select a project path first.");
                }
            }
        }
        return new ValidationResult();
    }


}



