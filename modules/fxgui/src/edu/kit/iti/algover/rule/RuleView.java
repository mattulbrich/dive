/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rule;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.Parameters;
import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.ProofRuleApplicationBuilder;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermParameter;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.rules.impl.ExhaustiveRule;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.util.RuleParameterDialog;
import javafx.beans.value.ObservableValue;
import javafx.css.PseudoClass;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.control.Dialog;
import javafx.scene.control.Label;
import javafx.scene.control.ScrollPane;
import javafx.scene.control.SelectionModel;
import javafx.scene.input.MouseEvent;
import javafx.scene.layout.StackPane;

public class RuleView extends StackPane {

    private static final PseudoClass PC_SELECTED = PseudoClass.getPseudoClass("selected");
    private static final PseudoClass PC_SELECTABLE = PseudoClass.getPseudoClass("selectable");

    private final Label ruleNameLabel;
    private final ProofRule rule;

    private ProofRuleApplication application;
    private ProofRuleApplication exApplication;
    private TermSelector selection;
    private RuleViewOverlay applicationOverlay;
    private boolean selectable;

    private final SelectionModel<RuleView> selectionModel;
    private final RuleApplicationListener listener;

    public RuleView(ProofRule rule, SelectionModel<RuleView> selectionModel, RuleApplicationListener listener) {
        this.rule = rule;
        this.selectionModel = selectionModel;
        this.listener = listener;
        this.selectable = false;

        getStyleClass().addAll("rule-view");
        setPadding(new Insets(4, 4, 4, 4));
        ruleNameLabel = new Label(rule.getName());
        ruleNameLabel.getStyleClass().add("rule-name");
        ruleNameLabel.setAlignment(Pos.CENTER);

        getChildren().setAll(ruleNameLabel);

        setOnMouseClicked(this::onClick);

        selectionModel.selectedItemProperty().addListener(this::onSelectedItemChanged);
        setPrefHeight(RuleGrid.RULE_CELL_HEIGHT);
        setPrefWidth(RuleGrid.RULE_CELL_WIDTH);
    }

    private void onSelectedItemChanged(ObservableValue<? extends RuleView> observableValue, RuleView selectedBefore, RuleView selectedNow) {
        boolean isSelected = selectedNow == this;
        pseudoClassStateChanged(PC_SELECTED, isSelected);
        if (isSelected) {
            listener.onPreviewRuleApplication(application);
        }
    }

    private void onClick(MouseEvent mouseEvent) {
        if (isSelectable()) {
            if (selectionModel.getSelectedItem() != this) {
                selectionModel.select(this);
                pseudoClassStateChanged(PC_SELECTED, true);
                requestFocus();
            } else {
                selectionModel.clearSelection();
            }
        }
    }

    public void considerApplication(ProofNode target, Sequent selection, TermSelector selector) {
        try {
            application = rule.considerApplication(target, selection, selector);
            if(rule.mayBeExhaustive()) {
                ExhaustiveRule exhaustiveRule = new ExhaustiveRule();
                Parameters params = new Parameters();
                params.putValue("on", new TermParameter(selector, selection));
                params.putValue("ruleName", rule.getName());
                exApplication = exhaustiveRule.considerApplication(target, params);
            } else {
                exApplication = ProofRuleApplicationBuilder.notApplicable(rule);
            }
            this.selection = selector;
            setSelectable(application != null && application.getApplicability() == ProofRuleApplication.Applicability.APPLICABLE);
            renderApplication();
        } catch (RuleException e) {
            try {
                application = rule.considerApplication(target, selection, null);
                this.selection = selector;
                setSelectable(application != null && application.getApplicability() == ProofRuleApplication.Applicability.APPLICABLE);
                renderApplication();
            } catch (RuleException ex) {
                System.err.println("Cannot consider Application: " + e);
                ex.printStackTrace();
            }
        }
    }

    private void renderApplication() {
        if (application != null) {
            applicationOverlay = new RuleViewOverlay(application, exApplication, listener, selection);
            getChildren().setAll(applicationOverlay, ruleNameLabel);
        } else {
            resetConsideration();
        }
    }

    public void resetConsideration() {
        application = null;
        applicationOverlay = null;
        setSelectable(false);
        getChildren().setAll(ruleNameLabel);
    }

    private void setSelectable(boolean selectable) {
        this.selectable = selectable;
        pseudoClassStateChanged(PC_SELECTABLE, selectable);
        if (!selectable) {
            if (selectionModel.getSelectedItem() == this) {
                selectionModel.clearSelection();
                pseudoClassStateChanged(PC_SELECTED, false);
            }
        }
    }

    public boolean isSelectable() {
        return selectable;
    }

    public ProofRuleApplication getApplication() {
        return application;
    }

    public ProofRule getRule() {
        return rule;
    }
}
