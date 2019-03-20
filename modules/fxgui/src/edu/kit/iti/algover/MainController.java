package edu.kit.iti.algover;

import com.jfoenix.controls.JFXButton;
import de.jensd.fx.glyphs.GlyphsDude;
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import edu.kit.iti.algover.browser.BrowserController;
import edu.kit.iti.algover.browser.FlatBrowserController;
import edu.kit.iti.algover.browser.entities.PVCEntity;
import edu.kit.iti.algover.browser.entities.PVCGetterVisitor;
import edu.kit.iti.algover.browser.entities.TreeTableEntity;
import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.dafnystructures.DafnyFunction;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.editor.EditorController;
import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.proof.*;
import edu.kit.iti.algover.references.*;
import edu.kit.iti.algover.rule.RuleApplicationController;
import edu.kit.iti.algover.rule.RuleApplicationListener;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.rules.impl.ExhaustiveRule;
import edu.kit.iti.algover.sequent.SequentActionListener;
import edu.kit.iti.algover.sequent.SequentTabViewController;
import edu.kit.iti.algover.timeline.TimelineLayout;
import edu.kit.iti.algover.util.CostumBreadCrumbBar;
import edu.kit.iti.algover.util.FormatException;
import edu.kit.iti.algover.util.StatusBarLoggingHandler;
import javafx.application.Platform;
import javafx.beans.value.ObservableValue;
import javafx.concurrent.Task;
import javafx.event.ActionEvent;
import javafx.scene.Parent;
import javafx.scene.control.*;
import javafx.scene.input.MouseEvent;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;
import org.controlsfx.control.StatusBar;

import java.io.File;
import java.io.IOException;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ExecutorService;
import java.util.logging.Level;
import java.util.logging.LogRecord;
import java.util.logging.Logger;
import java.util.stream.Collectors;

/**
 * Created by philipp on 27.06.17.
 */
public class MainController implements SequentActionListener, RuleApplicationListener {

    private final ProjectManager manager;
    private final ExecutorService executor;
    private final TimelineLayout timelineView;
    private final VBox view;

    // All controllers for the views, sorted from left-to-right in the way they appear in the GUI
    private final BrowserController browserController;
    private final EditorController editorController;
    private final SequentTabViewController sequentController;
    private final RuleApplicationController ruleApplicationController;
    private final ToolBar toolbar;
    private final StatusBar statusBar;
    private final StatusBarLoggingHandler statusBarLoggingHandler;
    private final JFXButton simpleStratButton;
    // REVIEW: Would <String> not be more appropriate?
    private final CostumBreadCrumbBar<Object> breadCrumbBar;


    public MainController(ProjectManager manager, ExecutorService executor) {
        this.manager = manager;
        this.executor = executor;
        this.browserController = new FlatBrowserController(manager.getProject(), manager.getAllProofs(), this::onClickPVCEdit);
        //this.browserController = new FileBasedBrowserController(manager.getProject(), manager.getAllProofs(), this::onClickPVCEdit);
        this.editorController = new EditorController(executor, manager.getProject().getBaseDir().getAbsolutePath());
        this.editorController.anyFileChangedProperty().addListener(this::onDafnyFileChangedInEditor);
        this.sequentController = new SequentTabViewController(this);
        this.ruleApplicationController = new RuleApplicationController(executor, this, manager);

        JFXButton saveButton = new JFXButton("Save", GlyphsDude.createIcon(FontAwesomeIcon.SAVE));
        JFXButton refreshButton = new JFXButton("Refresh", GlyphsDude.createIcon(FontAwesomeIcon.REFRESH));
        simpleStratButton = new JFXButton("Try Close All");

        saveButton.setOnAction(this::onClickSave);
        refreshButton.setOnAction(this::onClickRefresh);
        simpleStratButton.setOnAction(this::trivialStrat);

        TreeItem<Object> ti = getBreadCrumbModel();
        breadCrumbBar = new CostumBreadCrumbBar<>(ti, this::onCrumbSelected);
        breadCrumbBar.setStringFactory(this::getStringForTreeItem);
        breadCrumbBar.setSelectedCrumb(ti);


        this.toolbar = new ToolBar(saveButton, refreshButton, simpleStratButton);

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

        browserController.setSelectionListener(this::onSelectBrowserItem);

        Logger logger = Logger.getLogger(Logger.GLOBAL_LOGGER_NAME);
        statusBarLoggingHandler = new StatusBarLoggingHandler(statusBar);
        logger.addHandler(statusBarLoggingHandler);
        logger.setUseParentHandlers(false);
        logger.info("Project '" + manager.getName() + "' successfully loaded.");

        onClickRefresh(null);
    }

    private void trivialStrat(ActionEvent event) {
        Logger.getGlobal().info("Started try close all");
        Map<String, PVC> pvcMap = manager.getPVCByNameMap();
        for(Map.Entry<String, PVC> e : pvcMap.entrySet()) {
            String script = "";
            Proof p = manager.getProofForPVC(e.getKey());
            if (p.getProofStatus() != ProofStatus.CLOSED) {
                for (int i = 0; i < p.getProofRoot().getSequent().getAntecedent().size(); ++i) {
                    try {
                        ExhaustiveRule exRule = new ExhaustiveRule();
                        Parameters parameters = new Parameters();
                        parameters.putValue("ruleName", "substitute");
                        parameters.putValue("on", new TermParameter(new TermSelector("A." + i), p.getProofRoot().getSequent()));
                        ProofRuleApplication pra = exRule.considerApplication(p.getProofRoot(), parameters);

                        script += pra.getScriptTranscript();
                    } catch (FormatException ex) {
                        //TODO
                    } catch (RuleException ex) {
                        //TODO
                    }
                }
                for (int i = 0; i < p.getProofRoot().getSequent().getSuccedent().size(); ++i) {
                    try {
                        ExhaustiveRule exRule = new ExhaustiveRule();
                        Parameters parameters = new Parameters();
                        parameters.putValue("ruleName", "substitute");
                        parameters.putValue("on", new TermParameter(new TermSelector("S." + i), p.getProofRoot().getSequent()));
                        ProofRuleApplication pra = exRule.considerApplication(p.getProofRoot(), parameters);

                        script += pra.getScriptTranscript();
                    } catch (FormatException ex) {
                        //TODO
                    } catch (RuleException ex) {
                        //TODO
                    }
                }
                String letScript = script;
                script += "close;\n";
                p.setScriptTextAndInterpret(script);
                if(p.getFailException() != null) {
                    script = letScript + "boogie;\n";
                    p.setScriptTextAndInterpret(script);
                    if(p.getFailException() != null) {
                        p.setScriptTextAndInterpret(letScript);
                    }
                }
            }
        }
        sequentController.getActiveSequentController().tryMovingOnEx(); //SaG: was tryMovingOn()
        ruleApplicationController.resetConsideration();
        Logger.getGlobal().info("Finished try close all");

    }

    @SuppressWarnings("unchecked")
    private void onCrumbSelected(ObservableValue<?> observableValue, Object oldValue, Object newValue) {
        TreeItem<Object> item = (TreeItem<Object>) newValue;
        Platform.runLater(() -> {
            if (item.getValue() instanceof PVC) {
                PVC pvc = (PVC) item.getValue();
                try {
                    DafnyFile file = (DafnyFile) item.getParent().getParent().getValue();
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
                editorController.viewFile((DafnyFile) item.getValue());
                timelineView.moveFrameLeft();
                timelineView.moveFrameLeft();
                editorController.resetPVCSelection();
            }
            if (item.getValue() instanceof DafnyMethod) {
                if (item.getParent().getValue() instanceof DafnyFile) {
                    editorController.viewFile((DafnyFile) item.getParent().getValue());
                    timelineView.moveFrameLeft();
                    timelineView.moveFrameLeft();
                    editorController.resetPVCSelection();
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

    private void onClickSave(ActionEvent actionEvent) {
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
        onClickSave(null);
        editorController.resetExceptionLayer();
        Task<Void> t = new Task<Void>() {
            @Override
            protected Void call() throws Exception {
                manager.reload();
                return null;
            }
        };
        t.setOnSucceeded(event -> {
                manager.getAllProofs().values().forEach(p -> p.interpretScript());
                browserController.onRefresh(manager.getProject(), manager.getAllProofs());
                browserController.getView().setDisable(false);
                sequentController.getView().setDisable(false);
                ruleApplicationController.getView().setDisable(false);
                manager.getProject().getDafnyFiles().forEach(df -> editorController.viewFile(df));
                ruleApplicationController.onReset();
                simpleStratButton.setDisable(false);
                breadCrumbBar.setDisable(false);
                TreeItem<Object> ti = getBreadCrumbModel();
                breadCrumbBar.updateModel(ti);
                breadCrumbBar.setSelectedCrumb(ti);
                editorController.resetPVCSelection();
                sequentController.getActiveSequentController().clear();
                Logger.getLogger(Logger.GLOBAL_LOGGER_NAME).info("Successfully reloading project.");
        });

        //TODO somehow get proper exceptions and handling them
        t.setOnFailed(event -> {
            manager.getProject().getDafnyFiles().forEach(df -> editorController.viewFile(df));
            Logger.getLogger(Logger.GLOBAL_LOGGER_NAME).log(Level.SEVERE,
                    t.getException().getMessage(), t.getException());
            editorController.showException(t.getException());
            browserController.getView().setDisable(true);
            sequentController.getView().setDisable(true);
            ruleApplicationController.getView().setDisable(true);
            t.getException().printStackTrace();
        });

        t.setOnCancelled(event -> {
            Logger.getLogger(Logger.GLOBAL_LOGGER_NAME).severe("Reloading the project cancelled.");
        });

        executor.execute(t);
    }

    public void onClickPVCEdit(PVCEntity entity) {
        PVC pvc = entity.getPVC();
        breadCrumbBar.setSelectedCrumb(getTreeItemForPVC(pvc));
        editorController.viewFile(entity.getLocation());
        editorController.viewPVCSelection(pvc);
        Proof proof = manager.getProofForPVC(entity.getPVC().getIdentifier());
        // MU: currently proofs are not automatically interpreted and/or uptodate. Make sure they are.
        if (proof.getProofStatus() == ProofStatus.NON_EXISTING || proof.getProofStatus() == ProofStatus.CHANGED_SCRIPT)
            proof.interpretScript();
        sequentController.viewSequentForPVC(entity, proof);
        sequentController.getActiveSequentController().tryMovingOnEx();
        ruleApplicationController.resetConsideration();
        ruleApplicationController.getScriptController().setProof(proof);
        timelineView.moveFrameRight();
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

    public void onSelectBrowserItem(TreeTableEntity treeTableEntity) {
        DafnyFile file = treeTableEntity.getLocation();
        if (file != null) {
            editorController.viewFile(file);
            PVC pvc = treeTableEntity.accept(new PVCGetterVisitor());
            if (pvc != null) {
                editorController.viewPVCSelection(pvc);
                breadCrumbBar.setSelectedCrumb(getTreeItemForPVC(pvc));
            } else {
                editorController.resetPVCSelection();
                sequentController.getActiveSequentController().clear();
            }
        } else {
            sequentController.getActiveSequentController().clear();
        }
    }

    private TreeItem<Object> getTreeItemForPVC(PVC pvc) {
        List<TreeItem<Object>> files = breadCrumbBar.getModel().getChildren();
        List<TreeItem<Object>> methods = files.stream().flatMap(m -> m.getChildren().stream()).
                collect(Collectors.toList());
        List<TreeItem<Object>> pvcs = methods.stream().flatMap(m -> m.getChildren().stream()).
                filter(p -> ((PVC) (p.getValue())).equals(pvc)).collect(Collectors.toList());
        if (pvcs.size() == 1) {
            return pvcs.get(0);
        } else {
            System.out.println("this shoudnt happen. couldnt select breadcrumbitem for pvc");
            return null;
        }
    }

    @Override
    public void onClickSequentSubterm(TermSelector selector) {
        if (selector != null) {
            timelineView.moveFrameRight();
            ProofNode node = sequentController.getActiveSequentController().getActiveNode();
            if (node != null) {
                ruleApplicationController.considerApplication(node, node.getSequent(), selector);
            }
        }
    }

    @Override
    public void onRequestReferenceHighlighting(ProofTermReferenceTarget termRef) {
        Proof activeProof = sequentController.getActiveSequentController().getActiveProof();

        if (termRef != null) {
            System.out.println("Selected termReference = " + termRef);
            ReferenceGraph referenceGraph = activeProof.getGraph();
            //compute predecessors
            //Set<ReferenceTarget> predecessors = referenceGraph.allPredecessors(termRef);
            //Set<CodeReferenceTarget> codeReferenceTargets = filterCodeReferences(predecessors);
            Set<ProofTermReferenceTarget> proofTermReferenceTargets = referenceGraph.computeHistory(termRef, activeProof);

            Set<CodeReferenceTarget> codeReferenceTargets = referenceGraph.allPredecessorsWithType(termRef, CodeReferenceTarget.class);

            editorController.viewReferences(codeReferenceTargets);
            sequentController.viewReferences(proofTermReferenceTargets, termRef);

        } else {
            editorController.viewReferences(new HashSet<>());
        }
        try {
            Logger.getGlobal().info("Searched for references for selection "+termRef.getTermSelector().selectSubterm(termRef.getProofNodeSelector().get(activeProof).getSequent()));
        } catch (RuleException e) {

            Logger.getGlobal().warning("There was a problem computing the references.");
        }
    }

    /*
    private static Set<CodeReferenceTarget> filterCodeReferences(Set<ReferenceTarget> predecessors) {
        Set<CodeReferenceTarget> codeReferenceTargets = new HashSet<>();

        predecessors.forEach(reference -> {

            CodeReferenceTarget codeReferenceTarget = reference.accept(new GetReferenceTypeVisitor<>(CodeReferenceTarget.class));
            if (codeReferenceTarget != null) {
                codeReferenceTargets.add(codeReferenceTarget);
            }
        });
        return codeReferenceTargets;
    }

    private static Set<ProofTermReferenceTarget> filterTermReferences(Set<ReferenceTarget> predecessors){
        Set<ProofTermReferenceTarget> codeReferenceTargets = new HashSet<>();
        predecessors.forEach(reference -> {
            ProofTermReferenceTarget codeReferenceTarget = reference.accept(new GetReferenceTypeVisitor<>(ProofTermReferenceTarget.class));
            if (codeReferenceTarget != null) {
                codeReferenceTargets.add(codeReferenceTarget);
            }
        });
        return codeReferenceTargets;
    }*/

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
        sequentController.getActiveSequentController().getActiveProof().setScriptTextAndInterpret(newScript);
        ruleApplicationController.resetConsideration();
        sequentController.getActiveSequentController().tryMovingOnEx(); //SaG: was tryMovingOn()
        if(sequentController.getActiveSequentController().getActiveProof().getFailException() == null) {
            Logger.getLogger(Logger.GLOBAL_LOGGER_NAME).info("Successfully applied rule " + application.getRule().getName() + ".");
        }
    }

    @Override
    public void onRuleExApplication(ProofRule rule, TermSelector ts) {
        // This can be implemented as an incremental algorithm in the future here!
        // Currently, this will reset the script text completely. That means the
        // script has to be parsed and rebuilt completely.
        ruleApplicationController.applyExRule(rule, sequentController.getActiveSequentController().getActiveNode(), ts);
        ruleApplicationController.getRuleGrid().getSelectionModel().clearSelection();
        String newScript = ruleApplicationController.getScriptView().getText();
        sequentController.getActiveSequentController().getActiveProof().setScriptTextAndInterpret(newScript);
        ruleApplicationController.resetConsideration();
        sequentController.getActiveSequentController().tryMovingOnEx();
        if(sequentController.getActiveSequentController().getActiveProof().getFailException() == null) {
            Logger.getLogger(Logger.GLOBAL_LOGGER_NAME).info("Successfully applied rule " + rule.getName() + ".");
        }
    }

    @Override
    public void onScriptSave() {
        String pvcIdentifier = sequentController.getActiveSequentController().getActiveProof().getPVC().getIdentifier();
        try {
            manager.saveProofScriptForPVC(pvcIdentifier, sequentController.getActiveSequentController().getActiveProof());
            Logger.getLogger(Logger.GLOBAL_LOGGER_NAME).info("Successfully saved script " + pvcIdentifier + ".");
        } catch (IOException e) {
            Logger.getLogger(Logger.GLOBAL_LOGGER_NAME).severe("Error saving script.");
            e.printStackTrace();
        }
    }

    @Override
    public PVC getCurrentPVC() {
        return sequentController.getActiveSequentController().getActiveProof().getPVC();
    }

    @Override
    public ProofNode getCurrentProofNode() {
        return sequentController.getActiveSequentController().getActiveNode();
    }

    /**
     * when the user clicked somewhere in the proof script to change the proof node that should be viewed
     */
    @Override
    public void onSwitchViewedNode(ProofNodeSelector proofNodeSelector) {
        sequentController.viewProofNode(proofNodeSelector);
        ruleApplicationController.getScriptController().setSelectedNode(proofNodeSelector);
    }

    public Parent getView() {
        return view;
    }
}
