package edu.kit.iti.algover.rule;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Sequent;
import javafx.geometry.Pos;
import javafx.scene.control.Label;
import javafx.scene.layout.AnchorPane;
import javafx.scene.layout.StackPane;

public class RuleView extends StackPane {

    private final Label ruleNameLabel;
    private final ProofRule rule;

    private ProofRuleApplication application;
    private RuleApplicationOverlay applicationOverlay;

    public RuleView(ProofRule rule) {
        this.rule = rule;

        getStyleClass().addAll("rule-view");
        ruleNameLabel = new Label(rule.getName());
        ruleNameLabel.setAlignment(Pos.CENTER);

        getChildren().setAll(ruleNameLabel);
    }

    public void considerApplication(ProofNode target, Sequent selection, TermSelector selector) {
        try {
            application = rule.considerApplication(target, selection, selector);
        } catch (RuleException e) {
            System.err.println("Cannot consider Application!");
        }
        renderApplication();
    }

    private void renderApplication() {
        if (application != null) {
            int c = application.getBranchCount();
            String styleClass = c == 0 ? "closes" : c == 1 ? "non-splitting" : "splitting";
            getStyleClass().removeAll("closes", "non-splitting", "splitting");
            getStyleClass().add(styleClass);

            applicationOverlay = new RuleApplicationOverlay(application);
            getChildren().setAll(applicationOverlay, ruleNameLabel);
        } else {
            resetConsideration();
        }
    }

    public void resetConsideration() {
        application = null;
        applicationOverlay = null;
        getStyleClass().removeAll("closes", "non-splitting", "splitting");
        getChildren().setAll(ruleNameLabel);
    }
}
