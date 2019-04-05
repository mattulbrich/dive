package edu.kit.iti.algover;

import com.google.common.base.Charsets;
import com.google.common.io.CharStreams;
import de.jensd.fx.glyphs.GlyphsDude;
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.project.Configuration;
import edu.kit.iti.algover.project.DafnyProjectManager;
import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.project.XMLProjectManager;
import edu.kit.iti.algover.settings.ISettingsController;
import edu.kit.iti.algover.settings.ProjectSettingsController;
import edu.kit.iti.algover.settings.SettingsFactory;
import edu.kit.iti.algover.settings.SettingsWrapper;
import edu.kit.iti.algover.util.FormatException;
import javafx.application.Application;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.geometry.HPos;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.*;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.ColumnConstraints;
import javafx.scene.layout.GridPane;
import javafx.scene.layout.VBox;
import javafx.scene.web.WebEngine;
import javafx.scene.web.WebView;
import javafx.stage.DirectoryChooser;
import javafx.stage.FileChooser;
import javafx.stage.Stage;
import org.controlsfx.glyphfont.FontAwesome;
import sun.misc.IOUtils;

import java.awt.peer.TextComponentPeer;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.Optional;
import java.util.logging.Logger;

public class WelcomePane {
    @FXML
    WebView webView;

    @FXML
    private Button openFileChooser;

    @FXML
    private Button createProject;

    @FXML
    private Button openEmptyProject;

    @FXML
    private BorderPane rootPane;

    private Stage primaryStage;

    private Stage substage;



    public WelcomePane(Stage primaryStage, List<String> opendirectly){
        this.primaryStage = primaryStage;

        if(!opendirectly.isEmpty()){
            File absoluteFile = new File(opendirectly.get(0)).getAbsoluteFile();
            try {
                createAndExecuteMainController(absoluteFile, createProjectManager(absoluteFile));
            } catch (FormatException e) {
                e.printStackTrace();
            } catch (IOException e) {
                e.printStackTrace();
            } catch (DafnyParserException e) {
                e.printStackTrace();
            }
        } else {
            FXMLLoader loader = new FXMLLoader(getClass().getResource("WelcomePane.fxml"));
            loader.setController(this);
            try {
                loader.load();
                createWelcomeView();
            } catch (IOException e) {
                e.printStackTrace();
            }


        }


    }

    private void createWelcomeView() throws IOException {

        InputStream resourceAsStream = getClass().getResourceAsStream("welcomeText.html");
        String text = CharStreams.toString(new InputStreamReader(resourceAsStream, Charsets.UTF_8));

        WebEngine engine = webView.getEngine();
        engine.setUserStyleSheetLocation(getClass().getResource("webView.css").toString());
        engine.loadContent(text);


        openFileChooser.setText("Open project");
        openFileChooser.setStyle("-fx-font-size: 20");
        openFileChooser.setGraphic(GlyphsDude.createIcon(FontAwesomeIcon.FOLDER_OPEN));
        openFileChooser.setOnAction(this::handleFileChooserAction);

        createProject.setText("New project");
        createProject.setStyle("-fx-font-size: 20");
        createProject.setGraphic(GlyphsDude.createIcon(FontAwesomeIcon.FOLDER));
        createProject.setOnAction(this::createNewProjectHandler);

        openEmptyProject.setText("Empty project");
        openEmptyProject.setStyle("-fx-font-size: 20");
        openEmptyProject.setGraphic(GlyphsDude.createIcon(FontAwesomeIcon.FILE_CODE_ALT));
        openEmptyProject.setOnAction(handleEmptyProjectCreation(primaryStage));

    }

    public Parent getRootPane() {
        return rootPane;
    }

    public void createNewProjectHandler(ActionEvent event){
        createAndShowConfigPane(primaryStage);

    }

    private void handleFileChooserAction(ActionEvent actionEvent) {
        File projectFile;
        ProjectManager manager;
        try {
            projectFile = constructFileChooser();
            if(projectFile != null) {
                manager = createProjectManager(projectFile);
                // TODO Maybe don't do this initially (might hurt UX, when there are a lot of proofs)
                // manager.getAllProofs().values().forEach(proof -> proof.interpretScript());

                createAndExecuteMainController(projectFile, manager);
            } else {
                primaryStage.show();
            }



        } catch (FormatException e) {
            e.printStackTrace();
        } catch (IOException e) {
            e.printStackTrace();
        } catch (DafnyParserException e) {
            e.printStackTrace();
        }

    }



    private EventHandler<ActionEvent> handleEmptyProjectCreation(Stage primaryStage) {
        return event -> {
            DirectoryChooser dirChooser = new DirectoryChooser();

            dirChooser.setInitialDirectory(new File("doc/examples/"));
            dirChooser.setTitle("Select directory");
            //first select a directory
            File file = dirChooser.showDialog(primaryStage);


            if(file != null){
                //then a filename
                TextInputDialog dialog = new TextInputDialog("program.dfy");
                dialog.setTitle("Dafny file name");
                dialog.setHeaderText("Dafny file name");
                dialog.setContentText("Please enter the name for the empty Dafny file");
                Optional<String> filename = dialog.showAndWait();

                if (filename.isPresent()){
                    String s = file.getAbsolutePath() + File.separator + filename.get();
                    Path dfyMasterFile = null;
                    try {
                        dfyMasterFile = Files.createFile(Paths.get(s));
                        File file1 = dfyMasterFile.toFile();
                        DafnyProjectManager manager = new DafnyProjectManager(file1);
                        createAndExecuteMainController(file1, manager);
                    } catch (IOException e) {
                        e.printStackTrace();
                    } catch (DafnyParserException e) {
                        e.printStackTrace();
                    }
                }


            } else {
                System.out.println("file was null");
            }

        };
    }


    private void createAndShowConfigPane(Stage substage) {
        Configuration config = new Configuration();
        SettingsWrapper settings = new SettingsWrapper();
        settings.setConfig(config);
        Optional<ISettingsController> collect = SettingsFactory.getSettingsPanel(settings).stream()
                .filter(node -> node.getName().equals(ProjectSettingsController.NAME))
                .findAny();

        if(collect.isPresent()){
            BorderPane configPane = new BorderPane();
            //Outer scrollpane
            ScrollPane scrollPane = new ScrollPane();
            scrollPane.setFitToWidth(true);
            scrollPane.setContent(collect.get().getNode());

            configPane.setCenter(scrollPane);

            //Buttons
            ButtonBar buttonBar = new ButtonBar();
            Button applyConfig = new Button("Create Configuration");
            ButtonBar.setButtonData(applyConfig, ButtonBar.ButtonData.APPLY);
            applyConfig.setOnAction(event -> {
                //save settings, s.t., they are loadable using the standard loading mechanism
                ProjectManager manager = null;

                try {
                    collect.get().save();
                    if (config.isSaveAsXML()) {
                        manager = new XMLProjectManager(config.getBaseDir(), config.getConfigFile());
                    } else {
                        manager = new DafnyProjectManager(config.getMasterFile());
                    }
                    createAndExecuteMainController(config.getBaseDir(), manager);

                } catch (IOException e) {
                    Logger.getGlobal().warning("Invalid settings set, please review.");
                } catch (DafnyParserException e) {
                    Logger.getGlobal().severe("Project could not be created");
                    e.printStackTrace();
                } catch (FormatException e) {
                    Logger.getGlobal().severe("Project could not be created");
                    e.printStackTrace();
                }


            });

            Button cancelButton = new Button("Cancel");
            cancelButton.setOnAction(event -> {substage.setScene(rootPane.getScene());});

            ButtonBar.setButtonData(cancelButton, ButtonBar.ButtonData.CANCEL_CLOSE);
            buttonBar.getButtons().addAll(applyConfig, cancelButton);
            configPane.setBottom(buttonBar);
            Scene configurationScene = new Scene(configPane);
            substage.setScene(configurationScene);

        } else {
            BorderPane pane = new BorderPane();
            String error = "Could not create configuration creation dialog. Please contact the developers.";
            pane.setCenter(new TextArea(error));
            substage.setScene(new Scene(pane));
        }
    }

    private File constructFileChooser() {
        File projectFile;
        //Application.Parameters params = getParameters();
        //List<String> fileNames = params.getUnnamed();
        //if(fileNames.isEmpty()) {

            FileChooser chooser = new FileChooser();

            chooser.setTitle("Choose project folder");
            chooser.setInitialDirectory(new File("doc/examples/"));
            projectFile = chooser.showOpenDialog(primaryStage);
            ProjectManager manager;
            if (projectFile == null) {
                return null;
            }
       // }
        /*else {
            projectFile = new File(fileNames.get(0)).getAbsoluteFile();
        }*/
        return projectFile;

    }


    private void createAndExecuteMainController(File projectFile, ProjectManager manager) {
        MainController controller = new MainController(manager, AlgoVerApplication.SYNTAX_HIGHLIGHTING_EXECUTOR);

        primaryStage.close();
        Scene scene = new Scene(controller.getView());
        scene.getStylesheets().add(AlgoVerApplication.class.getResource("style.css").toExternalForm());
        substage = new Stage();
        substage.setScene(scene);
        substage.setWidth(900);
        substage.setHeight(700);
        substage.setTitle("AlgoVer - " + projectFile);
        substage.show();
    }

    private ProjectManager createProjectManager(File projectFile) throws FormatException, IOException, DafnyParserException {
        ProjectManager manager;
        if (projectFile.getName().endsWith(".xml")) {
            // Read all PVCs and update GUId
            manager = new XMLProjectManager(projectFile.getParentFile(), projectFile.getName());
        } else if (projectFile.getName().endsWith(".dfy")) {
            manager = new DafnyProjectManager(projectFile);
        } else {
            throw new IllegalArgumentException("AlgoVer supports only .dfy and .xml files.");
        }
        return manager;
    }

}
