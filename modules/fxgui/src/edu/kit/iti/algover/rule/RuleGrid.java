package edu.kit.iti.algover.rule;

import com.jfoenix.controls.JFXMasonryPane;
import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.scene.control.SelectionModel;
import javafx.scene.control.SingleSelectionModel;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

public class RuleGrid extends JFXMasonryPane {

    public static final double RULE_CELL_WIDTH = 140;
    public static final double RULE_CELL_HEIGHT = 80;
    public static final double SPACING = 4;

    private final List<RuleView> allRules;

    private final ObservableList<RuleView> rules;
    private final SelectionModel<RuleView> selectionModel;

    public RuleGrid() {
        this(new RuleView[0]);
    }

    public RuleGrid(RuleView... rules) {
        super();
        this.rules = FXCollections.observableArrayList(rules);
        this.allRules = new ArrayList<>(Arrays.asList(rules));
        this.selectionModel = new RuleSelectionModel();

        setCellWidth(RULE_CELL_WIDTH);
        setCellHeight(RULE_CELL_HEIGHT);
        setVSpacing(SPACING);
        setHSpacing(SPACING);
    }

    public void addRule(RuleView rule) {
        this.rules.add(rule);
        this.allRules.add(rule);
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

    public void filterRules() {
        filterRules(
                ruleView -> ruleView.getApplication() != null &&
                        ruleView.getApplication().getApplicability() != ProofRuleApplication.Applicability.NOT_APPLICABLE
        );
    }

    public void filterRules(Predicate<RuleView> filterFunction) {
        rules.clear();
        rules.addAll(allRules.stream().filter(
                ruleView -> filterFunction.test(ruleView)
        ).collect(Collectors.toList()));

        //REVIEW this should better be done dynamically but since it does not update automatically this at least
        //prevents that some arent shown at all
        rules.stream().forEach(ruleView -> {
            if (ruleView.getPrefWidth() == -1.0) {
                ruleView.setPrefWidth(140.0);
            }
        });
        rules.stream().forEach(ruleView -> {
            if (ruleView.getPrefHeight() == -1.0) {
                ruleView.setPrefHeight(80.0);
            }
        });
        rules.stream().forEach(ruleView -> ruleView.requestLayout());
        rules.stream().forEach(ruleView -> ruleView.autosize());

        this.getChildren().clear();
        this.getChildren().addAll(rules);
        requestLayout();
    }

    public List<RuleView> getAllRules() {
        return allRules;
    }
}
