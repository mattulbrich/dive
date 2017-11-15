package edu.kit.iti.algover.rule;

import com.jfoenix.controls.JFXMasonryPane;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.scene.control.SelectionModel;
import javafx.scene.control.SingleSelectionModel;

public class RuleGrid extends JFXMasonryPane {

    public static final double RULE_CELL_WIDTH = 140;
    public static final double RULE_CELL_HEIGHT = 80;
    public static final double SPACING = 4;

    private final ObservableList<RuleView> rules;
    private final SelectionModel<RuleView> selectionModel;

    public RuleGrid() {
        this(new RuleView[0]);
    }

    public RuleGrid(RuleView... rules) {
        super();
        this.rules = FXCollections.observableArrayList(rules);
        this.selectionModel = new RuleSelectionModel();

        setCellWidth(RULE_CELL_WIDTH);
        setCellHeight(RULE_CELL_HEIGHT);
        setVSpacing(SPACING);
        setHSpacing(SPACING);
    }

    public void addRule(RuleView rule) {
        this.rules.add(rule);
        this.getChildren().add(rule);
    }

    public SelectionModel<RuleView> getSelectionModel() {
        return selectionModel;
    }

    public ObservableList<RuleView> getRules() {
        return rules;
    }

    private class RuleSelectionModel extends SingleSelectionModel<RuleView> {
        @Override
        protected RuleView getModelItem(int i) {
            if (i < 0) {
                return null;
            }
            return rules.get(i);
        }

        @Override
        protected int getItemCount() {
            return rules.size();
        }
    }
}
