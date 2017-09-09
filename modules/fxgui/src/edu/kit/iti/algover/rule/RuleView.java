package edu.kit.iti.algover.rule;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import javafx.geometry.Pos;
import javafx.scene.control.Label;
import javafx.scene.layout.AnchorPane;
import javafx.scene.layout.StackPane;

public class RuleView extends StackPane {

    private final Label ruleNameLabel;
    private final AnchorPane anchorPane;
    private final ProofRule rule;

    public RuleView(ProofRule rule) {
        this.rule = rule;

        getStyleClass().addAll("rule-view");
        System.out.println(getStyleClass());
        ruleNameLabel = new Label(rule.getName());
        ruleNameLabel.setAlignment(Pos.CENTER);

        anchorPane = new AnchorPane();

        getChildren().setAll(ruleNameLabel, anchorPane);
    }

    public void considerApplication(ProofNode target, Sequent selection, TermSelector selector) {
        try {
            ProofRuleApplication application = rule.considerApplication(target, selection, selector);
            System.out.println(application);
        } catch (RuleException e) {
            System.err.println("Cannot consider Application!");
        }
    }
}
