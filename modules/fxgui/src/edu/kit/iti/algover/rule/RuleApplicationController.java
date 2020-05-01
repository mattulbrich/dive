/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rule;

import com.jfoenix.controls.JFXRadioButton;
import com.jfoenix.controls.JFXToggleButton;
import edu.kit.iti.algover.FxmlController;
import edu.kit.iti.algover.Lookup;
import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.referenceHighlighting.ReferenceHighlightingHandler;
import edu.kit.iti.algover.referenceHighlighting.ReferenceHighlightingObject;
import edu.kit.iti.algover.rule.script.ScriptController;
import edu.kit.iti.algover.rule.script.ScriptView;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.prettyprint.PrettyPrint;
import edu.kit.iti.algover.util.ExceptionDialog;
import javafx.application.Platform;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.fxml.FXML;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.control.SplitPane;
import javafx.scene.control.Toggle;
import javafx.scene.control.ToggleGroup;
import javafx.scene.layout.HBox;
import org.fxmisc.flowless.VirtualizedScrollPane;

import java.util.Collection;
import java.util.concurrent.ExecutorService;
import java.util.logging.Logger;
import java.util.stream.Collectors;

public class RuleApplicationController extends FxmlController implements ReferenceHighlightingHandler {

    @FXML
    private SplitPane splitPane;
    @FXML
    private Label termToConsider;

    @FXML
    private RuleGrid ruleGrid;

    @FXML
    private JFXRadioButton sortAlpha;

    @FXML
    private JFXRadioButton sortBranching;



    private final ScriptView scriptView;

    private final RuleApplicationListener listener;

    private final ScriptController scriptController;

    private final Logger logger;

    private final ProjectManager manager;

    private final ToggleGroup group = new ToggleGroup();


    public RuleApplicationController(ExecutorService executor, RuleApplicationListener listener, ProjectManager manager, Lookup lookup) {
        super("RuleApplicationView.fxml");
        this.listener = listener;
        this.scriptController = new ScriptController(executor, listener, lookup);
        this.scriptView = scriptController.getView();
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


        logger = Logger.getLogger(Logger.GLOBAL_LOGGER_NAME);
        this.manager = manager;

        for (ProofRule rule : manager.getProject().getAllProofRules()) {
            addProofRule(rule);
        }
        ruleGrid.getSelectionModel().selectedItemProperty().addListener(this::onSelectedItemChanged);
        VirtualizedScrollPane<ScriptView> proofScriptPane = new VirtualizedScrollPane<>(scriptView);
        splitPane.getItems().add(0, proofScriptPane);

    }

    public void addProofRule(ProofRule rule) {
        ruleGrid.addRule(new RuleView(rule, ruleGrid.getSelectionModel(), listener));
    }

    public void considerApplication(ProofNode target, Sequent selection, TermSelector selector) {
        try {
            Term term = selector.selectSubterm(selection);
            String prettyPrinted = new PrettyPrint().print(term, 60).toString();
            termToConsider.setText(prettyPrinted);
        } catch (RuleException e) {
            e.printStackTrace();
        }
        ruleGrid.getAllRules().forEach(ruleView -> ruleView.considerApplication(target, selection, selector));

        ruleGrid.filterRules();

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

    public ScriptView getScriptView() {
        return scriptView;
    }

    public ScriptController getScriptController() {
        return scriptController;
    }

    public void applyRule(ProofRuleApplication application) {
        try {
            resetConsideration();
            scriptController.insertTextForSelectedNode(application.getScriptTranscript()+"\n"); //SaG: removed newline character
        } catch(RuleException e) {
            Logger.getLogger(Logger.GLOBAL_LOGGER_NAME).severe("Error applying rule: " + e.getMessage());
        }
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
}
