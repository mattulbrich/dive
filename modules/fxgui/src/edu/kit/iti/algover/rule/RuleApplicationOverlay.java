package edu.kit.iti.algover.rule;

import edu.kit.iti.algover.rules.ProofRuleApplication;
import javafx.geometry.Pos;
import javafx.scene.control.Label;
import javafx.scene.layout.AnchorPane;

public class RuleApplicationOverlay extends AnchorPane {
    private final ProofRuleApplication application;

    public RuleApplicationOverlay(ProofRuleApplication application) {
        this.application = application;

        Label branchCount = new Label(application.getBranchCount() + " branches");
        branchCount.setAlignment(Pos.TOP_RIGHT);
        setRightAnchor(branchCount, 4.0);
        getChildren().add(branchCount);
    }
}
