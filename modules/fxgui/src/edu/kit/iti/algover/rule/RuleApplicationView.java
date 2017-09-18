package edu.kit.iti.algover.rule;

import javafx.geometry.Insets;
import javafx.scene.control.Label;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;

public class RuleApplicationView extends VBox {

    private final Label rulesLabel = new Label("Rules");
    private final Label termToConsider = new Label("");
    private final RuleGridView ruleGrid = new RuleGridView();

    public RuleApplicationView() {
        getStyleClass().add("rule-application-view");
        rulesLabel.getStyleClass().add("display-1");
        termToConsider.getStyleClass().add("code");

        HBox heading = new HBox(rulesLabel, termToConsider);
        heading.setSpacing(10);
        getChildren().setAll(heading, ruleGrid);
        VBox.setVgrow(ruleGrid, Priority.ALWAYS);
        setSpacing(4);

        setPadding(new Insets(10, 10, 10 ,10));
    }

    public RuleGridView getRuleGrid() {
        return ruleGrid;
    }

    public Label getTermToConsider() {
        return termToConsider;
    }
}
