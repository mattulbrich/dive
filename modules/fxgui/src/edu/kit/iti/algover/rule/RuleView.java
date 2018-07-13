package edu.kit.iti.algover.rule;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.util.RuleParameterDialog;
import javafx.beans.value.ObservableValue;
import javafx.css.PseudoClass;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.control.Dialog;
import javafx.scene.control.Label;
import javafx.scene.control.SelectionModel;
import javafx.scene.input.MouseEvent;
import javafx.scene.layout.StackPane;

public class RuleView extends StackPane {

    private static final PseudoClass PC_SELECTED = PseudoClass.getPseudoClass("selected");
    private static final PseudoClass PC_SELECTABLE = PseudoClass.getPseudoClass("selectable");

    private final Label ruleNameLabel;
    private final ProofRule rule;

    private ProofRuleApplication application;
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
            }
        }
    }

    private void renderApplication() {
        if (application != null) {
            applicationOverlay = new RuleViewOverlay(application, listener, selection);
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
}
