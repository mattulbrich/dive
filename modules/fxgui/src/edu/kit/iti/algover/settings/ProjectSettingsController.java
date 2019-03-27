package edu.kit.iti.algover.settings;

import com.jfoenix.controls.JFXButton;
import com.jfoenix.controls.JFXListView;
import com.sun.javafx.collections.ObservableListWrapper;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.project.*;
import edu.kit.iti.algover.util.*;
import javafx.application.Platform;
import javafx.beans.property.SimpleObjectProperty;
import javafx.collections.ObservableList;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.scene.Node;
import javafx.scene.control.*;
import javafx.scene.control.cell.TextFieldListCell;
import javafx.scene.layout.VBox;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.*;
import java.util.function.Supplier;
import java.util.logging.Logger;
import java.util.stream.Collectors;

import edu.kit.iti.algover.settings.ProjectSettings.Property;
import edu.kit.iti.algover.util.StringValidators.OptionStringValidator;
import javafx.stage.FileChooser;
import javafx.util.StringConverter;
import org.controlsfx.validation.ValidationResult;
import org.controlsfx.validation.ValidationSupport;
import org.controlsfx.validation.Validator;

import javax.xml.bind.JAXBException;

/**
 * Controller for the Project Settings View
 * @author S.Grebing
 */
public class ProjectSettingsController implements SettingsSupplier {

    public static final String NAME = "Project";

    private Node settingsPanel;

    @FXML
    private VBox container;

    @FXML
    private VBox projectConfigSettings;

    @FXML
    private TextField projectPath;

    @FXML
    private TextField configFileName;

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

    @FXML
    private CheckBox saveOption;

    private SimpleObjectProperty<Configuration> config = new SimpleObjectProperty<>(new Configuration(), "Configuration");


    private Map<String, String> currentSettings = null;

    private List<Pair<Supplier<String>, Property>> validators;

    private ValidationSupport validationSupport = new ValidationSupport();

    private boolean saveAsXML = false;

    /**
     * The ProjectManager for a loaded project
     */
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

        addProjectContents();
        addCellFactories();
        addValidationSupport();
        config.addListener((observable, oldValue, newValue) -> {
            if(newValue != null) {
                addProjectContents();
            }
        });
        managerProperty().addListener((observable, oldValue, newValue) -> {
            addProjectContents();
        });

    }

    private void addValidationSupport() {
        Platform.runLater(() -> {
           //  validationSupport.registerValidator(projectPath, true, XXX);
            //validationSupport.registerValidator(configFileName, true, getValidatorForType(InputType.FILE));
        });
    }



    /**
     * Add contents to the SettingsView
     */
    private void addProjectContents() {
        if(manager.get() != null) {
            Project p = manager.get().getProject();
            this.configFileName.setText(manager.get().getName());

            File baseDir = p.getBaseDir();
            this.projectPath.setText(baseDir.toString());

            //add Dafnyfiles
            List<DafnyFile> allDafnyFiles = p.getDafnyFiles();
            List<DafnyFile> libs = allDafnyFiles.stream().filter(dafnyFile -> dafnyFile.isInLibrary()).collect(Collectors.toList());
            List<DafnyFile> otherDafnyFiles = allDafnyFiles.stream().filter(dafnyFile -> !dafnyFile.isInLibrary()).collect(Collectors.toList());

            this.dafnyFiles.getItems().addAll(otherDafnyFiles.stream().map(dafnyFile -> dafnyFileToFile(dafnyFile)).collect(Collectors.toList()));

            this.libFiles.getItems().addAll(
                    libs.stream().map(dafnyFile -> dafnyFileToFile(dafnyFile)).collect(Collectors.toList()));

            //add settings
            ProjectSettings settings = p.getSettings();
            HashMap<String, String> newSettings = new HashMap<>();
            for (Property property : ProjectSettings.getDefinedProperties()) {
                newSettings.put(property.key, settings.getString(property.key));
            }
            currentSettings = newSettings;
            createSettingsFields();
        } else {
            createSettingsFields();
        }
    }

    /**
     * Transform a DafnyFile into a File
     * @param df
     * @return
     * @throws FileNotFoundException
     */
    private static File dafnyFileToFile(DafnyFile df){
        File f = new File(df.getFilename());
        if(f.exists()){
            return f;
        } else {
            return new File("");
        }
    }

    /**
     * Add cellfactories for lists
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
                ObservableList<String> olist =
                        new ObservableListWrapper<>(Util.map(options, Object::toString));
                String value = currentSettings.get(property.key);
                ChoiceBox<String> choiceBox = new ChoiceBox<>(olist);
                if(value != null) {
                    choiceBox.setValue(value);
                }
                projectConfigSettings.getChildren().add(choiceBox);
                validators.add(new Pair<>(() -> choiceBox.getValue(), property));
            } else {
                TextField textField = new TextField();
                String value = currentSettings.get(property.key);
                if(value != null) {
                    textField.setText(value);
                }
               /* textField.textProperty().addListener((observable, oldValue, newValue) -> {
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
                });*/
                projectConfigSettings.getChildren().add(textField);
                Pair<Supplier<String>, Property> e = new Pair<>(() -> textField.getText(), property);
                Platform.runLater(() -> { validationSupport.registerValidator(textField, new SettingsValidatorAdapter(e.snd.validator));});
                validators.add(e);

            }
        }

    }

    @Override
    public Node getNode() {
        return settingsPanel;
    }

    /**
     * Save current configuration and request for reloading project
     * @author M.Ulrbich
     * @modfied S.Grebing
     *
     */
    @Override
    public void save() {
        String pathText = projectPath.getText();

        Configuration newConfig = new Configuration();
        newConfig.setDafnyFiles(dafnyFiles.getItems());
        newConfig.setLibFiles(libFiles.getItems());

        Map<String, String> newProperties = new HashMap<>();
        for (Pair<Supplier<String>, Property> value : validators) {
                String v = value.fst.get();
                if(!v.trim().isEmpty()) {
                    newProperties.put(value.snd.key, v);
                }
        }

        newConfig.setSettings(newProperties);
        File baseDir = new File(pathText);
        if(saveAsXML){
            try {
                String property = System.getProperty("file.separator");
                File filename = new File(baseDir + property + configFileName);
                if(filename.exists()){
                //TODO
                }
                ConfigXMLLoader.saveConfigFile(newConfig, filename);
            } catch (JAXBException e) {
                Logger.getGlobal().warning("Could not save configuration file");
                e.printStackTrace();
            }
        } else {
            try {
                manager.get().saveProject();
            } catch (IOException e) {
                Logger.getGlobal().severe("Error saving project settings");
            }
        }


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

    //region: ActionHandler

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
    private void setSaveOption(){
        saveAsXML = saveOption.isSelected();
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
                initialDir=newFile;
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


