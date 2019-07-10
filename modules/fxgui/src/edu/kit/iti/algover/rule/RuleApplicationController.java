/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rule;

import edu.kit.iti.algover.FxmlController;
import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rule.script.ScriptController;
import edu.kit.iti.algover.rule.script.ScriptView;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.rules.impl.ExhaustiveRule;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.prettyprint.PrettyPrint;
import javafx.beans.value.ObservableValue;
import javafx.fxml.FXML;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.control.SplitPane;
import org.fxmisc.flowless.VirtualizedScrollPane;

import java.util.concurrent.ExecutorService;
import java.util.logging.Logger;
import java.util.stream.Collectors;

public class RuleApplicationController extends FxmlController {

    @FXML
    private SplitPane splitPane;
    @FXML
    private Label termToConsider;
    @FXML
    private RuleGrid ruleGrid;

    private final ScriptView scriptView;

    private final RuleApplicationListener listener;

    private final ScriptController scriptController;

    private final Logger logger;

    private final ProjectManager manager;

    public RuleApplicationController(ExecutorService executor, RuleApplicationListener listener, ProjectManager manager) {
        super("RuleApplicationView.fxml");
        this.listener = listener;
        this.scriptController = new ScriptController(executor, listener);
        this.scriptView = scriptController.getView();

        logger = Logger.getLogger(Logger.GLOBAL_LOGGER_NAME);
        this.manager = manager;

        for (ProofRule rule : manager.getProject().getAllProofRules()) {
            addProofRule(rule);
        }

        ruleGrid.getSelectionModel().selectedItemProperty().addListener(this::onSelectedItemChanged);
        splitPane.getItems().add(new VirtualizedScrollPane<>(scriptView));
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
        ruleGrid.getAllRules().forEach(ruleView -> {
            ruleView.considerApplication(target, selection, selector);
        });
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

    public void applyExRule(ProofRule rule, ProofNode pn, TermSelector ts) {
        try {
            ExhaustiveRule exRule = new ExhaustiveRule();
            Parameters parameters = new Parameters();
            parameters.putValue(ExhaustiveRule.RULE_NAME_PARAM, rule.getName());
            parameters.putValue(ExhaustiveRule.ON_PARAM_REQ, new TermParameter(ts, pn.getSequent()));
            // MU: I have changed this from considerapplication to makeApplication
            // This piece of code looks like suboptimal special casing. (see RuleView)
            ProofRuleApplication pra = exRule.makeApplication(pn, parameters);
            resetConsideration();
            scriptController.insertTextForSelectedNode(pra.getScriptTranscript());
            logger.info("Applied rule " + rule.getName() + " exhaustively.");
        } catch (RuleException e) {
            //TODO handle exeptions
            logger.severe("Error while trying to apply rule " + rule.getName() + " exhaustive.");
        }
    }

    public void applyRule(ProofRuleApplication application) {
        try {
            resetConsideration();
            scriptController.insertTextForSelectedNode(application.getScriptTranscript()); //SaG: removed newline character
        } catch(RuleException e) {
            Logger.getLogger(Logger.GLOBAL_LOGGER_NAME).severe("Error applying rule: " + e.getMessage());
        }
    }

    public void onReset() {
        ruleGrid.setAllRules(manager.getProject().getAllProofRules().stream()
                .map(rule -> new RuleView(rule, ruleGrid.getSelectionModel(), listener))
                .collect(Collectors.toList()));
    }
}
