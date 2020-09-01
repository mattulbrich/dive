/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover;

import com.jfoenix.controls.JFXButton;
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import de.jensd.fx.glyphs.fontawesome.utils.FontAwesomeIconFactory;
import edu.kit.iti.algover.browser.BrowserController;
import edu.kit.iti.algover.browser.FlatBrowserController;
import edu.kit.iti.algover.browser.TreeTableEntityContextMenuStrategyHelper;
import edu.kit.iti.algover.browser.callvisualization.CallVisualizationDialog;
import edu.kit.iti.algover.browser.callvisualization.CallVisualizationModel;
import edu.kit.iti.algover.browser.entities.DafnyEntityGetterVisitor;
import edu.kit.iti.algover.browser.entities.PVCEntity;
import edu.kit.iti.algover.browser.entities.TreeTableEntity;
import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.dafnystructures.DafnyFunction;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.editor.EditorController;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.PVCCollection;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofStatus;
import edu.kit.iti.algover.referenceHighlighting.ReferenceGraphController;
import edu.kit.iti.algover.rule.RuleApplicationController;
import edu.kit.iti.algover.rule.RuleApplicationListener;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.sequent.SequentTabViewController;
import edu.kit.iti.algover.settings.SettingsController;
import edu.kit.iti.algover.settings.SettingsFactory;
import edu.kit.iti.algover.settings.SettingsWrapper;
import edu.kit.iti.algover.timeline.TimelineLayout;
import edu.kit.iti.algover.util.CostumBreadCrumbBar;
import edu.kit.iti.algover.util.ExceptionDialog;
import edu.kit.iti.algover.util.StatusBarLoggingHandler;
import javafx.beans.value.ObservableValue;
import javafx.concurrent.Task;
import javafx.event.ActionEvent;
import javafx.scene.control.Alert;
import javafx.scene.control.ButtonBar;
import javafx.scene.control.ButtonType;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.Label;
import javafx.scene.control.MenuItem;
import javafx.scene.control.ToolBar;
import javafx.scene.control.TreeItem;
import javafx.scene.input.MouseEvent;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Pane;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;
import javafx.stage.Stage;
import org.controlsfx.control.StatusBar;
import org.controlsfx.dialog.ProgressDialog;

import java.io.File;
import java.io.IOException;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.concurrent.ExecutorService;
import java.util.logging.Level;
import java.util.logging.LogRecord;
import java.util.logging.Logger;
import java.util.prefs.Preferences;

import static javafx.application.Platform.runLater;

/**
 * Created by philipp on 27.06.17.
 */
public class MainController implements RuleApplicationListener {

    //system preferences
    public static final Preferences systemprefs = Preferences.userNodeForPackage(MainController.class);

    private Lookup lookup = new Lookup();

    private final ProjectManager manager;
    private final ExecutorService executor;
    private final TimelineLayout timelineView;
    private final VBox view;

    // All controllers for the views, sorted from left-to-right in the way they appear in the GUI
    private final BrowserController browserController;
    private final EditorController editorController;
    private final SequentTabViewController sequentController;
    private final RuleApplicationController ruleApplicationController;
    private final ReferenceGraphController referenceGraphController;
    private final ToolBar toolbar;
    private final StatusBar statusBar;
    private final StatusBarLoggingHandler statusBarLoggingHandler;
    private final JFXButton simpleStratButton;
    private final JFXButton settingsButton;
    private final JFXButton aboutButton;
    private final JFXButton backButton;
    // REVIEW: Would <String> not be more appropriate?
    private final CostumBreadCrumbBar<Object> breadCrumbBar;


    public MainController(ProjectManager manager, ExecutorService executor) {
        this.manager = manager;
        this.executor = executor;
        this.browserController = new FlatBrowserController(manager.getProject(), manager.getAllProofs(), this::onClickPVCEdit);
        //this.browserController = new FileBasedBrowserController(manager.getProject(), manager.getAllProofs(), this::onClickPVCEdit);
        this.editorController = new EditorController(executor, manager.getProject().getBaseDir().getAbsolutePath(), this.lookup);
        this.editorController.anyFileChangedProperty().addListener(this::onDafnyFileChangedInEditor);
        this.sequentController = new SequentTabViewController(lookup);
        this.ruleApplicationController = new RuleApplicationController(executor, this, manager, this.lookup);
        this.referenceGraphController = new ReferenceGraphController(this.lookup);

        PropertyManager.getInstance().projectManager.set(manager);
        PropertyManager.getInstance().currentProject.set(manager.getProject());

        JFXButton saveButton = new JFXButton("Save", FontAwesomeIconFactory.get().createIcon(FontAwesomeIcon.SAVE));
        JFXButton refreshButton = new JFXButton("Refresh", FontAwesomeIconFactory.get().createIcon(FontAwesomeIcon.REFRESH));
        simpleStratButton = new JFXButton("Try Close All", FontAwesomeIconFactory.get().createIcon(FontAwesomeIcon.PLAY_CIRCLE));
        settingsButton = new JFXButton("Settings", FontAwesomeIconFactory.get().createIcon(FontAwesomeIcon.COGS));
        aboutButton = new JFXButton("About", FontAwesomeIconFactory.get().createIcon(FontAwesomeIcon.INFO_CIRCLE));
        backButton = new JFXButton("Project Chooser", FontAwesomeIconFactory.get().createIcon(FontAwesomeIcon.ARROW_LEFT));

        saveButton.setOnAction(this::onClickSaveVisibleContent);
        refreshButton.setOnAction(this::onClickRefresh);
        simpleStratButton.setOnAction(this::trivialStrat);
        settingsButton.setOnAction(this::openSettingsWindow);
        aboutButton.setOnAction(this::openAboutWindow);
        backButton.setOnAction(this::backToWelcome);

        TreeItem<Object> ti = getBreadCrumbModel();
        breadCrumbBar = new CostumBreadCrumbBar<>(ti, this::onCrumbSelected);
        breadCrumbBar.setStringFactory(this::getStringForTreeItem);
        breadCrumbBar.setSelectedCrumb(ti);

        final Pane spacer = new Pane();
        HBox.setHgrow(spacer, Priority.ALWAYS);
        spacer.setMinSize(10, 1);

        this.toolbar = new ToolBar(saveButton, refreshButton, simpleStratButton, settingsButton, spacer, backButton, aboutButton);

        this.statusBar = new StatusBar();
        this.statusBar.setOnMouseClicked(this::onStatusBarClicked);
        ContextMenu contextMenu = new ContextMenu();
        statusBar.setContextMenu(contextMenu);

        this.timelineView = new TimelineLayout(
                browserController.getView(),
                editorController.getView(),
                sequentController.getView(),
                ruleApplicationController.getRuleApplicationView());
        timelineView.setDividerPosition(0.2);

        this.view = new VBox(toolbar, breadCrumbBar, timelineView, statusBar);
        VBox.setVgrow(timelineView, Priority.ALWAYS);

        createContextMenu();
        Logger logger = Logger.getLogger(Logger.GLOBAL_LOGGER_NAME);
        statusBarLoggingHandler = new StatusBarLoggingHandler(statusBar);
        logger.addHandler(statusBarLoggingHandler);
        logger.setUseParentHandlers(false);
        logger.info("Project '" + manager.getName() + "' successfully loaded.");

        //Add property listener
        PropertyManager.getInstance().selectedTerm.addListener(((observable, oldValue, newValue) -> onClickSequentSubterm(newValue)));
        PropertyManager.getInstance().currentPVC.addListener(((observable, oldValue, newValue) -> onSelectBrowserItem(newValue)));
        PropertyManager.getInstance().selectedTermForReference.addListener(((observable, oldValue, newValue) -> timelineView.setFramePosition(1)));

        onClickRefresh(null);
    }

    private void backToWelcome(ActionEvent event) {
        Alert closing = new Alert(Alert.AlertType.CONFIRMATION);
        Label content = new Label("You are about to close the current project and switch back to the project chooser.");
        Label content2 = new Label("All unsaved progress will get lost.");
        VBox vBox = new VBox(content, content2);
        closing.getDialogPane().setContent(vBox);
        closing.getDialogPane().setHeaderText("Switching back to Project Chooser");
        closing.setResizable(true);
        closing.onShownProperty().addListener(e -> runLater(() -> closing.setResizable(false)));
        Optional<ButtonType> buttonType = closing.showAndWait();
        if(buttonType.get().getButtonData().equals(ButtonBar.ButtonData.OK_DONE)) {
            ((Stage) getView().getScene().getWindow()).close();

            Stage stage = new Stage();
            stage.setTitle("DIVE");
            AlgoVerApplication.startApplication(stage, Collections.emptyList());
        }
    }

    private void openAboutWindow(ActionEvent actionEvent) {
        AboutWindow about = null;
        try {
            about = new AboutWindow();
            about.showAndWait();
        } catch (IOException e) {
            Logger.getGlobal().warning("Error while loading about text");
        }

    }

    private void openSettingsWindow(ActionEvent actionEvent) {
        SettingsWrapper settings = new SettingsWrapper();
        settings.setConfig(manager.getConfiguration());
        settings.setCurrentManager(manager);
        settings.setSystemPrefs(systemprefs);
        settings.setLookup(this.lookup);
        double height = this.getView().getScene().getWindow().getHeight();
        double width = this.getView().getScene().getWindow().getWidth();
        //later lookup
        SettingsController ctrl = new SettingsController(this, height, width);
        ctrl.getItems().setAll(SettingsFactory.getSettingsPanel(settings));
        ctrl.showAndWait();
    }

    private void createContextMenu() {
        ContextMenu browserContextMenu = browserController.getBrowserContextMenu();
        MenuItem tryCloseAll = new MenuItem("Try to close selected PVC(s)");
        tryCloseAll.setOnAction(this::trivialStratContextMenuAction);
        browserContextMenu.getItems().addAll(tryCloseAll);
        MenuItem showCalled = new MenuItem("Show called and calling entities");
        showCalled.setOnAction(this::showCalledEntities);
        browserContextMenu.getItems().addAll(showCalled);

    }


    private void showCalledEntities(ActionEvent actionEvent) {
        try {
            TreeItem<TreeTableEntity> selectedItem = browserController.getView().getSelectionModel().getSelectedItem();
            TreeTableEntity value = selectedItem.getValue();
            DafnyDecl accept = value.accept(new DafnyEntityGetterVisitor());
            if(accept != null){

                Collection<DafnyTree> calls = manager.getProject().getCallgraph().getCalls(accept);
                Collection<DafnyTree> callsites = manager.getProject().getCallgraph().getCallsites(accept);

                if(!calls.isEmpty() || !callsites.isEmpty()){
                    CallVisualizationModel model = new CallVisualizationModel(manager.getProject().getCallgraph(), accept, calls, callsites);
                    CallVisualizationDialog d = new CallVisualizationDialog(model, lookup);
                    d.setResizable(true);
                    d.onShownProperty().addListener(e -> runLater(() -> d.setResizable(false)));
                    Optional<ButtonType> buttonType = d.showAndWait();
                    if(buttonType.get() == ButtonType.CLOSE){
                        editorController.removeReferenceHighlighting();
                    }
                }

            } else {
                 Logger.getGlobal().info("Please select a method or function in the browser tree.");
            }
        } catch (NullPointerException npe){
            Logger.getGlobal().info("Please select an item in the browser tree.");

        }
    }

    private void trivialStratContextMenuAction(ActionEvent event){
        try {
            TreeItem<TreeTableEntity> selectedItem = browserController.getView().getSelectionModel().getSelectedItem();
            TreeTableEntity value = selectedItem.getValue();
            List<String> pvcNames = value.accept(new TreeTableEntityContextMenuStrategyHelper());
            //System.out.println("pvcNames = " + pvcNames);
            applyTrivialStrategy(pvcNames);
        } catch (NullPointerException npe){
            Logger.getGlobal().info("Please select an item in the browser tree.");

        }

    }

    private void trivialStrat(ActionEvent event) {
        Map<String, PVC> pvcMap = manager.getPVCByNameMap();
        applyTrivialStrategy(pvcMap.keySet());
    }

    private void applyTrivialStrategy(Collection<String> pvcNames) {
        Task<Integer> t1 = new Task<Integer>() {
            @Override
            protected Integer call() {
                int prog = 0;
                int failed = 0;
                for(String pvcName : pvcNames) {
                    Proof p = manager.getProofForPVC(pvcName);
                    p.interpretScript();
                    if (p.getProofStatus() != ProofStatus.CLOSED) {
                        String oldScript = p.getScript();
                        String script = "boogie;\n";
                        p.setScriptTextAndInterpret(script);
                        if (p.getFailException() != null) {
                            p.setScriptTextAndInterpret(oldScript + "boogie;");
                            if (p.getFailException() != null) {
                                p.setScriptText(oldScript);
                                p.interpretScript();
                                failed++;
                            }
                        }
                    }
                    prog++;
                    updateProgress(prog, pvcNames.size());
                }

                runLater(() -> {
                    sequentController.getActiveSequentController().tryMovingOnEx(); //SaG: was tryMovingOn()
                    ruleApplicationController.resetConsideration();
                });
                return pvcNames.size() - failed;
            }
        };
        ProgressDialog progressDialog = new ProgressDialog(t1);
        //workaround for KDE systems and GTK based Desktops
        progressDialog.setResizable(true);
        progressDialog.onShownProperty().addListener(e -> runLater(() -> progressDialog.setResizable(false)));


        t1.setOnSucceeded($ -> runLater(() -> {

            Alert a = new Alert(Alert.AlertType.INFORMATION);
            a.setTitle("Applied strategy");
            a.setHeaderText("Successfully applied strategy and closed "
                                    + t1.valueProperty().get() + " of " + pvcNames.size() + " PVCs.");
            //workaround for KDE systems and GTK based Desktops
            a.setResizable(true);
            a.onShownProperty().addListener(e -> runLater(() -> a.setResizable(false)));
            a.showAndWait();
            Logger.getGlobal().info("Successfully applied strategy and closed "
                    + t1.valueProperty().get() + " of " + pvcNames.size() + " PVCs.");
        }));
        t1.setOnCancelled($ -> runLater(() -> Logger.getGlobal().severe("Strategy was cancelled.")));
        progressDialog.setHeaderText("Applying strategy to " + pvcNames.size() + " PVCs. Please wait.");
        progressDialog.setTitle("Applying strategy");
        progressDialog.getDialogPane().getButtonTypes().add(ButtonType.CANCEL);
        progressDialog.setOnCloseRequest(event -> t1.cancel());
        new Thread(t1).start();
    }

    @SuppressWarnings("unchecked")
    private void onCrumbSelected(ObservableValue<?> observableValue, Object oldValue, Object newValue) {
        TreeItem<Object> item = (TreeItem<Object>) newValue;
        runLater(() -> {
            if (item.getValue() instanceof PVC) {
                PVC pvc = (PVC) item.getValue();
                try {
                    DafnyFile file = (DafnyFile) item.getParent().getParent().getValue();
                    PropertyManager.getInstance().currentFile.set(file);
                    PropertyManager.getInstance().currentPVC.set(pvc);
                    timelineView.moveFrameLeft();
                    timelineView.moveFrameLeft();
                    onClickPVCEdit(new PVCEntity(manager.getProofForPVC(pvc.getIdentifier()), pvc, file));
                } catch (NullPointerException e) {
                    Logger.getLogger(Logger.GLOBAL_LOGGER_NAME).warning("Could not select pvc.");
                    e.printStackTrace();
                } catch (ClassCastException c) {
                    Logger.getLogger(Logger.GLOBAL_LOGGER_NAME).warning("Could not select pvc.");
                }
            }
            if (item.getValue() instanceof DafnyFile) {
                PropertyManager.getInstance().currentFile.set((DafnyFile) item.getValue());
                //editorController.viewFile(manager.getProject().getBaseDir(), (DafnyFile) item.getValue());
                timelineView.moveFrameLeft();
                timelineView.moveFrameLeft();
                PropertyManager.getInstance().currentPVC.set(null);
                //editorController.resetPVCSelection();
            }
            if (item.getValue() instanceof DafnyMethod) {
                if (item.getParent().getValue() instanceof DafnyFile) {
                    PropertyManager.getInstance().currentFile.set((DafnyFile) item.getParent().getValue());
                    //editorController.viewFile(manager.getProject().getBaseDir(), (DafnyFile) item.getParent().getValue());
                    timelineView.moveFrameLeft();
                    timelineView.moveFrameLeft();
                    PropertyManager.getInstance().currentPVC.set(null);
                    //editorController.resetPVCSelection();
                }
            }
        });
    }

    private void onStatusBarClicked(MouseEvent event) {
        ContextMenu contextMenu = statusBar.getContextMenu();
        contextMenu.getItems().clear();
        for (LogRecord logRecord : statusBarLoggingHandler.getHistory(5)) {
            MenuItem item = new MenuItem(logRecord.getMessage());
            item.setOnAction(ev -> {
                Throwable ex = logRecord.getThrown();
                if(ex != null) {
                    editorController.showException(ex);
                }
            });
            contextMenu.getItems().add(item);
        }

        contextMenu.show(statusBar, event.getScreenX(), event.getScreenY());
    }

    public TreeItem<Object> getBreadCrumbModel() {
        TreeItem<Object> lastitem = null;
        TreeItem<Object> root = new TreeItem<>("root");
        for (DafnyFile f : manager.getProject().getDafnyFiles()) {
            if (f.isInLibrary()) {
                continue;
            }
            TreeItem<Object> fileChild = new TreeItem<>(f.getFilename());
            fileChild.setValue(f);
            root.getChildren().add(fileChild);
            for (DafnyMethod m : f.getMethods()) {
                TreeItem<Object> methodChild = new TreeItem<>(m.getName());
                methodChild.setValue(m);
                fileChild.getChildren().add(methodChild);
                PVCCollection collection = manager.getProject().getPVCsFor(m);
                for (PVC pvc : collection.getContents()) {
                    lastitem = new TreeItem<>(pvc.getIdentifier());
                    lastitem.setValue(pvc);
                    methodChild.getChildren().add(lastitem);
                }
            }
            for (DafnyFunction fi : f.getFunctions()) {
                TreeItem<Object> functionChild = new TreeItem<>(fi.getName());
                functionChild.setValue(fi);
                fileChild.getChildren().add(functionChild);
                PVCCollection collection = manager.getProject().getPVCsFor(fi);
                for (PVC pvc : collection.getContents()) {
                    lastitem = new TreeItem<>(pvc.getIdentifier());
                    lastitem.setValue(pvc);
                    functionChild.getChildren().add(lastitem);
                }
            }
            for(DafnyClass dc : f.getClasses()) {
                for (DafnyMethod m : dc.getMethods()) {
                    TreeItem<Object> methodChild = new TreeItem<>(m.getName());
                    methodChild.setValue(m);
                    fileChild.getChildren().add(methodChild);
                    PVCCollection collection = manager.getProject().getPVCsFor(m);
                    for (PVC pvc : collection.getContents()) {
                        lastitem = new TreeItem<>(pvc.getIdentifier());
                        lastitem.setValue(pvc);
                        methodChild.getChildren().add(lastitem);
                    }
                }
                for (DafnyFunction fi : dc.getFunctions()) {
                    TreeItem<Object> functionChild = new TreeItem<>(fi.getName());
                    functionChild.setValue(fi);
                    fileChild.getChildren().add(functionChild);
                    PVCCollection collection = manager.getProject().getPVCsFor(fi);
                    for (PVC pvc : collection.getContents()) {
                        lastitem = new TreeItem<>(pvc.getIdentifier());
                        lastitem.setValue(pvc);
                        functionChild.getChildren().add(lastitem);
                    }
                }
            }
        }
        return root;
    }

    /**
     * Updates the text of the StatusBar
     *
     * @param text the new text
     */
    public void setStatusBarText(String text) {
        statusBar.setText(text);
    }

    /**
     * Updates the progress of the StatusBar
     *
     * @param progress the new progress (should be between 0 and 1)
     */
    public void setStatusBarProgress(double progress) {
        statusBar.setProgress(progress);
    }

    private void onClickSaveVisibleContent(ActionEvent actionEvent) {
        // TODO: Save the project
        try {
            editorController.saveAllFiles();
            manager.saveProject();
            Logger.getLogger(Logger.GLOBAL_LOGGER_NAME).info("Successfully saved project.");
        } catch (IOException e) {
            Alert alert = new Alert(Alert.AlertType.INFORMATION, "Error saving the project.");
            alert.showAndWait();
        }
    }

    private void onClickRefresh(ActionEvent actionEvent) {
        // TODO implement it asynchronously:
        // Jobs should get queued / Buttons disabled while an action runs, but the UI shouldn't freeze!
        onClickSaveVisibleContent(null);
        editorController.resetExceptionLayer();
        refreshHelper();

    }

    private void refreshHelper(){
        Task<Void> t = new Task<Void>() {
            @Override
            protected Void call() throws Exception {
                manager.reload();
                return null;
            }
        };

        t.setOnSucceeded(event -> {
            //manager.getAllProofs().values().forEach(p -> p.interpretScript());
            browserController.onRefresh(this.manager.getProject(), this.manager.getAllProofs());
            browserController.getView().setDisable(false);
            sequentController.getView().setDisable(false);
            ruleApplicationController.getView().setDisable(false);
            manager.getProject().getDafnyFiles().forEach(df ->
                    editorController.viewFile(manager.getProject().getBaseDir(), df));
            ruleApplicationController.onReset();
            simpleStratButton.setDisable(false);
            breadCrumbBar.setDisable(false);
            TreeItem<Object> ti = getBreadCrumbModel();
            breadCrumbBar.updateModel(ti);
            breadCrumbBar.setSelectedCrumb(ti);
            editorController.resetPVCSelection();
            sequentController.getActiveSequentController().clear();
            showStartTimeLineConfiguration();
            Logger.getLogger(Logger.GLOBAL_LOGGER_NAME).info("Successfully reloaded project.");
        });

        //TODO somehow get proper exceptions and handling them
        t.setOnFailed(event -> {
            manager.getProject().getDafnyFiles().forEach(df ->
                    editorController.viewFile(manager.getProject().getBaseDir(),df));
            Logger.getLogger(Logger.GLOBAL_LOGGER_NAME).log(Level.SEVERE,
                    t.getException().getMessage(),
                    t.getException());
            editorController.showException(t.getException());
            browserController.getView().setDisable(true);
            sequentController.getView().setDisable(true);
            ruleApplicationController.getView().setDisable(true);
            t.getException().printStackTrace();
            ExceptionDialog ed = new ExceptionDialog(t.getException());
            ed.showAndWait();
        });

        t.setOnCancelled(event -> Logger.getLogger(Logger.GLOBAL_LOGGER_NAME).severe("Reloading the project cancelled."));

        executor.execute(t);
    }

    private void showStartTimeLineConfiguration() {
        boolean moveLeftPosible = true;
        while(moveLeftPosible){
            moveLeftPosible = timelineView.moveFrameLeft();
        }
    }

    public void onClickPVCEdit(PVCEntity entity) {
        //Proof proof = manager.getProofForPVC(entity.getPVC().getIdentifier());
        //// MU: currently proofs are not automatically interpreted and/or uptodate. Make sure they are.
        //if (proof.getProofStatus() == ProofStatus.NON_EXISTING || proof.getProofStatus() == ProofStatus.CHANGED_SCRIPT)
        //    proof.interpretScript();
        ruleApplicationController.resetConsideration();
        timelineView.moveFrameRight();
    }

    /**
     * Refresh all GUI contents including the tabs in the DafnyCode Tab Pane
     */
    public void reloadWholeGUIcontents() {
        //editorController.refreshTabView(manager.getProject().getDafnyFiles()); will open another editor
        // tab with same file
        // use instead
        editorController.reloadAllOpenFiles();
        refreshHelper();
    }

    public void onDafnyFileChangedInEditor(ObservableValue<? extends Boolean> observable, Boolean oldValue, Boolean newValue) {
        if (newValue) {
            browserController.getView().setDisable(true);
            sequentController.getView().setDisable(true);
            ruleApplicationController.getView().setDisable(true);
            simpleStratButton.setDisable(true);
            breadCrumbBar.setDisable(true);
            editorController.resetPVCSelection();
        } /*else {
            browserController.getView().setDisable(false);
            sequentController.getView().setDisable(false);
            ruleApplicationController.getView().setDisable(false);
        }*/
    }

    private String getStringForTreeItem(TreeItem<Object> item) {
        Object value = item.getValue();
        if (value instanceof DafnyFile) {
            File f = new File(((DafnyFile) value).getFilename());
            return f.getName();
        }
        if (value instanceof DafnyMethod) {
            return ((DafnyMethod) value).getName();
        }
        if (value instanceof PVC) {
            return ((PVC) value).getIdentifier();
        }
        if (value instanceof DafnyFunction) {
            return ((DafnyFunction) value).getName();
        }
        return "error";
    }

    public void onSelectBrowserItem(PVC pvc) {
        if (pvc != null) {
            breadCrumbBar.setSelectedCrumb(pvc);
        }
    }

    public void onClickSequentSubterm(TermSelector selector) {
        if (selector != null) {
            timelineView.moveFrameRight();
        }
    }

    @Override
    public void onPreviewRuleApplication(ProofRuleApplication application) {
        sequentController.getActiveSequentController().viewProofApplicationPreview(application);
    }

    @Override
    public void onResetRuleApplicationPreview() {
        sequentController.getActiveSequentController().resetProofApplicationPreview();
    }

    @Override
    public void onRuleApplication(ProofRuleApplication application) {
        // This can be implemented as an incremental algorithm in the future here!
        // Currently, this will reset the script text completely. That means the
        // script has to be parsed and rebuilt completely.
        ruleApplicationController.applyRule(application);
        ruleApplicationController.getRuleGrid().getSelectionModel().clearSelection();
        String newScript = ruleApplicationController.getScriptView().getText();
        PropertyManager.getInstance().currentProof.get().setScriptTextAndInterpret(newScript);
        PropertyManager.getInstance().currentProofStatus.set(PropertyManager.getInstance().currentProof.get().getProofStatus());
        ruleApplicationController.resetConsideration();
        sequentController.getActiveSequentController().tryMovingOnEx(); //SaG: was tryMovingOn()
        if(PropertyManager.getInstance().currentProof.get().getFailException() == null) {
            Logger.getLogger(Logger.GLOBAL_LOGGER_NAME).info("Successfully applied rule " + application.getRule().getName() + ".");
        }
    }

    @Override
    public void onScriptSave() {
        String pvcIdentifier = PropertyManager.getInstance().currentProof.get().getPVC().getIdentifier();
        try {
            manager.saveProofScriptForPVC(pvcIdentifier, PropertyManager.getInstance().currentProof.get());
            Logger.getLogger(Logger.GLOBAL_LOGGER_NAME).info("Successfully saved script " + pvcIdentifier + ".");
        } catch (IOException e) {
            Logger.getLogger(Logger.GLOBAL_LOGGER_NAME).severe("Error saving script.");
            e.printStackTrace();
        }
    }

    public VBox getView() {
        return view;
    }
}
