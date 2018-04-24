package edu.kit.iti.algover;

import com.jfoenix.controls.JFXButton;
import de.jensd.fx.glyphs.GlyphsDude;
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import edu.kit.iti.algover.browser.BrowserController;
import edu.kit.iti.algover.browser.FlatBrowserController;
import edu.kit.iti.algover.browser.entities.PVCEntity;
import edu.kit.iti.algover.browser.entities.PVCGetterVisitor;
import edu.kit.iti.algover.browser.entities.TreeTableEntity;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.editor.EditorController;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.proof.*;
import edu.kit.iti.algover.references.CodeReference;
import edu.kit.iti.algover.references.GetReferenceTypeVisitor;
import edu.kit.iti.algover.references.ProofTermReference;
import edu.kit.iti.algover.references.Reference;
import edu.kit.iti.algover.rule.RuleApplicationController;
import edu.kit.iti.algover.rule.RuleApplicationListener;
import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.sequent.SequentActionListener;
import edu.kit.iti.algover.sequent.SequentController;
import edu.kit.iti.algover.timeline.TimelineLayout;
import edu.kit.iti.algover.util.FormatException;
import edu.kit.iti.algover.util.StatusBarLoggingHandler;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.concurrent.Task;
import javafx.event.ActionEvent;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.control.Alert;
import javafx.scene.control.Button;
import javafx.scene.control.ToolBar;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;
import org.controlsfx.control.StatusBar;

import java.io.IOException;
import java.util.HashSet;
import java.util.Set;
import java.util.concurrent.ExecutorService;
import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.Logger;

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
    private final SequentController sequentController;
    private final RuleApplicationController ruleApplicationController;
    private final ToolBar toolbar;
    private final StatusBar statusBar;


    public MainController(ProjectManager manager, ExecutorService executor) {
        this.manager = manager;
        this.executor = executor;
        this.browserController = new FlatBrowserController(manager.getProject(), manager.getAllProofs(), this::onClickPVCEdit);
        //this.browserController = new FileBasedBrowserController(manager.getProject(), manager.getAllProofs(), this::onClickPVCEdit);
        this.editorController = new EditorController(executor, manager.getProject().getBaseDir().getAbsolutePath());
        this.editorController.anyFileChangedProperty().addListener(this::onDafnyFileChangedInEditor);
        this.sequentController = new SequentController(this);
        this.ruleApplicationController = new RuleApplicationController(executor, this);

        JFXButton saveButton = new JFXButton("Save", GlyphsDude.createIcon(FontAwesomeIcon.SAVE));
        JFXButton refreshButton = new JFXButton("Refresh", GlyphsDude.createIcon(FontAwesomeIcon.REFRESH));

        saveButton.setOnAction(this::onClickSave);
        refreshButton.setOnAction(this::onClickRefresh);

        this.toolbar = new ToolBar(saveButton, refreshButton);

        this.statusBar = new StatusBar();
        this.statusBar.setText("Load successful.");

        this.timelineView = new TimelineLayout(
                browserController.getView(),
                editorController.getView(),
                sequentController.getView(),
                ruleApplicationController.getRuleApplicationView());
        timelineView.setDividerPosition(0.2);

        this.view = new VBox(toolbar, timelineView, statusBar);
        VBox.setVgrow(timelineView, Priority.ALWAYS);

        browserController.setSelectionListener(this::onSelectBrowserItem);

        Logger logger = Logger.getLogger(Logger.GLOBAL_LOGGER_NAME);
        logger.addHandler(new StatusBarLoggingHandler(statusBar));
        logger.setUseParentHandlers(false);
    }

    /**
     * Updates the text of the StatusBar
     * @param text the new text
     */
    public void setStatusBarText(String text) {
        statusBar.setText(text);
    }

    /**
     * Updates the progress of the StatusBar
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
        } catch (IOException e) {
            Alert alert = new Alert(Alert.AlertType.INFORMATION, "Error saving the project.");
            alert.showAndWait();
        }
    }

    private void onClickRefresh(ActionEvent actionEvent) {
        // TODO: Implement refreshing
        // Also implement it asynchronously:
        // Jobs should get queued / Buttons disabled while an action runs, but the UI shouldn't freeze!
        Task<Boolean> t = new Task<Boolean>() {
            @Override
            protected Boolean call() throws Exception {
                try {
                    manager.reload();
                } catch (IOException e) {
                    return false;
                }
                return true;
            }
        };
        executor.execute(t);
        t.setOnSucceeded(event -> {
            if(t.getValue()) {
                System.out.println("reload worked");
                browserController.onRefresh(manager.getProject(), manager.getAllProofs());
                browserController.getView().setDisable(false);
                sequentController.getView().setDisable(false);
                ruleApplicationController.getView().setDisable(false);
            } else {
                Alert alert = new Alert(Alert.AlertType.INFORMATION, "Error refreshing the project.");
                alert.showAndWait();
            }
        });
    }

    public void onClickPVCEdit(PVCEntity entity) {
        PVC pvc = entity.getPVC();
        editorController.viewFile(entity.getLocation());
        editorController.viewPVCSelection(pvc);
        Proof proof = manager.getProofForPVC(entity.getPVC().getIdentifier());
        // MU: currently proofs are not automatically interpreted and/or uptodate. Make sure they are.
        if(proof.getProofStatus() == ProofStatus.NON_EXISTING  || proof.getProofStatus() == ProofStatus.CHANGED_SCRIPT)
            proof.interpretScript();
        sequentController.viewSequentForPVC(entity, proof);
        ruleApplicationController.resetConsideration();
        ruleApplicationController.getScriptController().setProof(proof);
        timelineView.moveFrameRight();
    }

    public void onDafnyFileChangedInEditor(ObservableValue<? extends Boolean> observable, Boolean oldValue, Boolean newValue) {
        if(newValue) {
            browserController.getView().setDisable(true);
            sequentController.getView().setDisable(true);
            ruleApplicationController.getView().setDisable(true);
        } /*else {
            browserController.getView().setDisable(false);
            sequentController.getView().setDisable(false);
            ruleApplicationController.getView().setDisable(false);
        }*/
    }

    public void onSelectBrowserItem(TreeTableEntity treeTableEntity) {
        DafnyFile file = treeTableEntity.getLocation();
        if (file != null) {
            editorController.viewFile(file);
            PVC pvc = treeTableEntity.accept(new PVCGetterVisitor());
            if (pvc != null) {
                editorController.viewPVCSelection(pvc);
            } else {
                editorController.resetPVCSelection();
            }
        }
    }

    @Override
    public void onClickSequentSubterm(TermSelector selector) {
        timelineView.moveFrameRight();
        ProofNode node = sequentController.getActiveNode();
        if (node != null) {
            ruleApplicationController.considerApplication(node, node.getSequent(), selector);
        }
    }

    @Override
    public void onRequestReferenceHighlighting(ProofTermReference termRef) {
        if (termRef != null) {
            Set<Reference> predecessors = sequentController.getReferenceGraph().allPredecessors(termRef);
            Set<CodeReference> codeReferences = filterCodeReferences(predecessors);
            editorController.viewReferences(codeReferences);
        } else {
            editorController.viewReferences(new HashSet<>());
        }
    }

    private static Set<CodeReference> filterCodeReferences(Set<Reference> predecessors) {
        Set<CodeReference> codeReferences = new HashSet<>();
        predecessors.forEach(reference -> {
            CodeReference codeReference = reference.accept(new GetReferenceTypeVisitor<>(CodeReference.class));
            if (codeReference != null) {
                codeReferences.add(codeReference);
            }
        });
        return codeReferences;
    }

    @Override
    public void onPreviewRuleApplication(ProofRuleApplication application) {
        sequentController.viewProofApplicationPreview(application);
    }

    @Override
    public void onResetRuleApplicationPreview() {
        sequentController.resetProofApplicationPreview();
    }

    @Override
    public void onRuleApplication(ProofRuleApplication application) {
        // This can be implemented as an incremental algorithm in the future here!
        // Currently, this will reset the script text completely. That means the
        // script has to be parsed and rebuilt completely.
        ruleApplicationController.applyRule(application);
        ruleApplicationController.getRuleGrid().getSelectionModel().clearSelection();
        String newScript = ruleApplicationController.getScriptView().getText();
        sequentController.getActiveProof().setScriptTextAndInterpret(newScript);
        sequentController.tryMovingOn();
        ruleApplicationController.resetConsideration();
    }

    @Override
    public void onRuleExApplication(ProofRule rule, TermSelector ts) {
        // This can be implemented as an incremental algorithm in the future here!
        // Currently, this will reset the script text completely. That means the
        // script has to be parsed and rebuilt completely.
        ruleApplicationController.applyExRule(rule, sequentController.getActiveNode(), ts);
        ruleApplicationController.getRuleGrid().getSelectionModel().clearSelection();
        String newScript = ruleApplicationController.getScriptView().getText();
        sequentController.getActiveProof().setScriptTextAndInterpret(newScript);
        sequentController.tryMovingOn();
        ruleApplicationController.resetConsideration();
    }

    @Override
    public void onScriptSave() {
        String pvcIdentifier = sequentController.getActiveProof().getPVC().getIdentifier();
        try {
            manager.saveProofScriptForPVC(pvcIdentifier, sequentController.getActiveProof());
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    /**
     * when the user clicked somewhere in the proof script to change the proof node that should be viewed
     */
    @Override
    public void onSwitchViewedNode(ProofNodeSelector proofNodeSelector) {
        sequentController.viewProofNode(proofNodeSelector);
    }

    public Parent getView() {
        return view;
    }
}
