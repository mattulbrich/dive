package edu.kit.iti.algover.rule;

import edu.kit.iti.algover.rules.ProofRuleApplication;
import javafx.geometry.Pos;
import javafx.scene.control.Label;
import javafx.scene.layout.AnchorPane;

public class RuleViewOverlay extends AnchorPane {
    private final ProofRuleApplication application;

    public RuleViewOverlay(ProofRuleApplication application) {
        this.application = application;

        int count = application.getBranchCount();

        Label branchCount = new Label(count + fromPlural(count, " branch", " branches"));
        branchCount.setAlignment(Pos.TOP_RIGHT);
        branchCount.getStyleClass().add("branch-count");
        setRightAnchor(branchCount, 4.0);
        getChildren().add(branchCount);
    }

    private static String fromPlural(int count, String singular, String plural) {
        if (count == 1) return singular;
        else return plural;
    }
}
