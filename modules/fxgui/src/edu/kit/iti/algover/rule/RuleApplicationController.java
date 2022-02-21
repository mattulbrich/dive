/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rule;

import com.jfoenix.controls.JFXRadioButton;
import edu.kit.iti.algover.FxmlController;
import edu.kit.iti.algover.Lookup;
import edu.kit.iti.algover.PropertyManager;
import edu.kit.iti.algover.nuscript.ScriptAST;
import edu.kit.iti.algover.nuscript.parser.Scripts;
import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofStatus;
import edu.kit.iti.algover.referenceHighlighting.ReferenceHighlightingHandler;
import edu.kit.iti.algover.referenceHighlighting.ReferenceHighlightingObject;
import edu.kit.iti.algover.rule.script.BlocklyController;
import edu.kit.iti.algover.rule.script.ScriptTextController;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.prettyprint.PrettyPrint;
import edu.kit.iti.algover.timeline.TimelineFactory;
import edu.kit.iti.algover.util.ExceptionDialog;
import javafx.beans.value.ObservableValue;
import javafx.fxml.FXML;
import javafx.scene.Node;
import javafx.scene.control.*;
import javafx.scene.layout.VBox;

import java.io.IOException;
import java.util.concurrent.ExecutorService;
import java.util.logging.Logger;
import java.util.stream.Collectors;

public class RuleApplicationController extends FxmlController implements ReferenceHighlightingHandler {

    @FXML
    private SplitPane splitPane;
    @FXML
    private Label termToConsider;

    @FXML
    private VBox buttonBox;

    @FXML
    private Button btInsertCases;

    @FXML
    private Button btReplay;

    @FXML
    private Button btToggleView;

    @FXML
    private Label lbUnsavedScript;

    @FXML
    private RuleGrid ruleGrid;

    @FXML
    private JFXRadioButton sortAlpha;

    @FXML
    private JFXRadioButton sortBranching;

    @FXML
    private VBox scriptView;

    private BlocklyController scriptRepWeb;
    private ScriptTextController scriptRepText;

    private final RuleApplicationListener listener;

    private final Logger logger;

    private final ProjectManager manager;

    private final ToggleGroup group = new ToggleGroup();


    public RuleApplicationController(ExecutorService executor, RuleApplicationListener listener, ProjectManager manager, Lookup lookup) {
        super("RuleApplicationView.fxml");
        this.listener = listener;

        // Could be a collection
        this.scriptRepWeb = new BlocklyController();
        this.scriptRepText = new ScriptTextController(executor);
        lookup.register(this, RuleApplicationController.class);
        lookup.register(this, ReferenceHighlightingHandler.class);

        this.sortAlpha.setToggleGroup(group);
        this.sortBranching.setToggleGroup(group);
        this.group.selectedToggleProperty().addListener((ObservableValue<? extends Toggle> observable, Toggle oldValue, Toggle newValue) -> {
           String selectedButton = ((JFXRadioButton) newValue).getId();

           if(selectedButton.equals("sortAlpha")){
               ruleGrid.removeAllComparators();
               ruleGrid.addComparator(RuleGridComparator.compareAlphaOrder);
           }
           if(selectedButton.equals("sortBranching")){
               ruleGrid.removeAllComparators();
               ruleGrid.addComparator(RuleGridComparator.compareBranching);
           }
        });
       
/*        this.sortAlpha.selectedProperty().addListener((observable, oldValue, newValue) -> {
            if(newValue){
                ruleGrid.addComparator(RuleGridComparator.compareAlphaOrder);
            } else {
                ruleGrid.removeComparator(RuleGridComparator.compareAlphaOrder);
            }
        });

        this.sortBranching.selectedProperty().addListener((observable, oldValue, newValue) -> {
            if(newValue){
                ruleGrid.addComparator(RuleGridComparator.compareBranching);
            } else {
                ruleGrid.removeComparator(RuleGridComparator.compareBranching);
            }
        });*/

        PropertyManager.getInstance().selectedTerm.addListener(((observable, oldValue, newValue) -> {
                if (newValue != null && PropertyManager.getInstance().currentProofNode.get() != null) {
                    considerApplication(
                    PropertyManager.getInstance().currentProofNode.get(),
                    PropertyManager.getInstance().currentProofNode.get().getSequent(),
                    PropertyManager.getInstance().selectedTerm.get());
                }

        }));
        PropertyManager.getInstance().currentProofNode.addListener(((observable, oldValue, newValue) -> {
            if (newValue != null) {
                considerApplication(
                        PropertyManager.getInstance().currentProofNode.get(),
                        PropertyManager.getInstance().currentProofNode.get().getSequent(),
                        PropertyManager.getInstance().selectedTerm.get());
            }
        }));
        PropertyManager.getInstance().currentProofStatus.addListener(((observable, oldValue, newValue) -> {
            if(PropertyManager.getInstance().currentProofNode.get() != null) {
                considerApplication(
                        PropertyManager.getInstance().currentProofNode.get(),
                        PropertyManager.getInstance().currentProofNode.get().getSequent(),
                        PropertyManager.getInstance().selectedTerm.get()
                );
            }

            if (newValue == ProofStatus.FAILING) {
                showExceptionDialogsLastRun();
            }

        }));


        scriptRepText.getView().textProperty().addListener((observable, oldValue, newValue) -> {
            String pvcIdentifier = PropertyManager.getInstance().currentProof.get().getPVC().getIdentifier();
            String inFile = "";
            try {
                inFile = manager.loadScriptForPVC(pvcIdentifier);
            } catch (IOException ioex) {
                ExceptionDialog ed = new ExceptionDialog(ioex);
                ed.showAndWait();
            }
            inFile = inFile.replaceAll("[\\n\\t ]", "");
            String textFieldReference = newValue.replaceAll("[\\n\\t ]", "");
            lbUnsavedScript.setVisible(!inFile.equals(textFieldReference));
        });

        PropertyManager.getInstance().currentlyDisplayedView.addListener((observable, oldValue, newValue) -> {
            if (newValue.intValue() == TimelineFactory.DefaultViewPosition.SEQUENT_RULE.index) {
                scriptRepWeb.getView().requestFocus();
            }
        });

        logger = Logger.getLogger(Logger.GLOBAL_LOGGER_NAME);
        this.manager = manager;

        for (ProofRule rule : manager.getProject().getAllProofRules()) {
            addProofRule(rule);
        }
        ruleGrid.getSelectionModel().selectedItemProperty().addListener(this::onSelectedItemChanged);

        btInsertCases.setOnAction(event -> {
            scriptRepWeb.onInsertCases();

        });

        btReplay.setOnAction(event -> {
            onScriptSave();
            scriptRepText.runScript();
            scriptRepWeb.highlightScriptErrors();
            lbUnsavedScript.setVisible(false);
        });


        scriptRepText.getView().prefHeightProperty().bind(buttonBox.heightProperty());

        this.scriptView.getChildren().setAll(scriptRepWeb.getView());

        btToggleView.setOnAction(event -> {
            if (scriptView.getChildren().contains(scriptRepWeb.getView())) {
                this.scriptView.getChildren().setAll(scriptRepText.getView());
            } else if (scriptView.getChildren().contains(scriptRepText.getView())) {
                this.scriptView.getChildren().setAll(scriptRepWeb.getView());
            }

        });

        // Blockly view (and ScriptCodeView) are not greyed out when disabled
        // (for some FX reason). Set the style here manually.
        scriptView.disabledProperty().addListener((observable, oldValue, newValue) ->
        {
            for (Node child: scriptView.getChildren()) {
                child.setDisable(newValue);
                if (newValue) {
                    child.setStyle("-fx-opacity: 0.4; -fx-font-size: " + scriptRepText.getView().fontsizeProperty().get() + "pt");
                } else {
                    child.setStyle("-fx-opacity: 1; -fx-font-size: " + scriptRepText.getView().fontsizeProperty().get() + "pt");
                }
            }
        });

    }

    private void showExceptionDialogsLastRun() {
        Proof proof = PropertyManager.getInstance().currentProof.get();
        for (Exception ex: proof.getFailures()) {
            Logger.getGlobal().severe(ex.getMessage());
            ExceptionDialog ed = new ExceptionDialog(ex);
            ed.show();
        }
    }

    public void addProofRule(ProofRule rule) {
        ruleGrid.addRule(new RuleView(rule, ruleGrid.getSelectionModel(), listener));
    }

    public void considerApplication(ProofNode target, Sequent selection, TermSelector selector) {
        if(target != null) {
            // isValidForSequent could be avoided if selector is properly reset on proofchange
            if (selector != null && selector.isValidForSequent(selection)) {
                try {
                    Term term = selector.selectSubterm(selection);
                    String prettyPrinted = new PrettyPrint().print(term, 60).toString();
                    termToConsider.setText(prettyPrinted);
                } catch (RuleException e) {
                    e.printStackTrace();
                }
            } else {
                termToConsider.setText("");
            }
            ruleGrid.getAllRules().forEach(ruleView -> ruleView.considerApplication(target, selection, selector));

            ruleGrid.filterRules();
        }
    }

    public void resetConsideration() {
        ruleGrid.getRules().forEach(RuleView::resetConsideration);
        termToConsider.setText("");
        ruleGrid.filterRules();
    }

    private void onSelectedItemChanged(ObservableValue<? extends RuleView> obs, RuleView before, RuleView selected) {
        if (selected == null) {
            listener.onResetRuleApplicationPreview();
        }
    }

    public Node getRuleApplicationView() {
        return view;
    }

    public RuleGrid getRuleGrid() {
        return ruleGrid;
    }

    // TODO: consider reimplementation
    public void applyRule(ProofRuleApplication application) {
        try {
            resetConsideration();
            // TODO: create new Statement directly from ProofRuleApplication.
            ScriptAST.Script newLine = Scripts.parseScript(application.getScriptTranscript());
            scriptRepWeb.insertAtCurrentPosition(application, newLine);
            scriptRepWeb.runScript();
            lbUnsavedScript.setVisible(true);

        } catch(RuleException e) {
            Logger.getLogger(Logger.GLOBAL_LOGGER_NAME).severe("Error applying rule: " + e.getMessage());
        }

        scriptRepWeb.highlightScriptErrors();
    }

    public void onReset() {
        ruleGrid.setAllRules(manager.getProject().getAllProofRules().stream()
                .map(rule -> new RuleView(rule, ruleGrid.getSelectionModel(), listener))
                .collect(Collectors.toList()));
    }

    @Override
    public void handleReferenceHighlighting(ReferenceHighlightingObject references) {
        //do nothing at the moment
    }

    @Override
    public void removeReferenceHighlighting() {
        //Do nothing at the moment
    }

    public Node getScriptView() {
        return this.scriptRepText.getView();
    }

    public void onScriptSave() {
        String pvcIdentifier = PropertyManager.getInstance().currentProof.get().getPVC().getIdentifier();
        try {
            manager.saveProofScripts();
            Logger.getLogger(Logger.GLOBAL_LOGGER_NAME).info("Successfully saved script " + pvcIdentifier + ".");
        } catch (IOException e) {
            Logger.getLogger(Logger.GLOBAL_LOGGER_NAME).severe("Error saving script.");
            e.printStackTrace();
        }
    }

    public void notifyEverythingSaved() {
        lbUnsavedScript.setVisible(false);
    }

}
