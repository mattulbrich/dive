/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rule;

import com.jfoenix.controls.JFXMasonryPane;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import javafx.application.Platform;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.geometry.Insets;
import javafx.scene.Node;
import javafx.scene.control.SelectionModel;
import javafx.scene.control.SingleSelectionModel;

import java.util.*;
import java.util.function.Predicate;
import java.util.stream.Collectors;

public class RuleGrid extends JFXMasonryPane {

    public static final double RULE_CELL_WIDTH = 140;
    public static final double RULE_CELL_HEIGHT = 80;
    public static final double SPACING = 4;


    private List<RuleView> allRules;

    private final ObservableList<RuleView> rules;
    private final SelectionModel<RuleView> selectionModel;

    private List<Comparator<RuleView>> activeComparator = new ArrayList<>();


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
        //SaG: Do not remove, causes null values in super-object  if not called.
        layoutChildren();
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

        Platform.runLater(() -> {

            ObservableList<Node> children = this.getChildren();
            int size = children.size();
            if(size > 0 ){
                children.clear();
            }

            children.addAll(rules);
            requestLayout();

        });


        this.getChildren().clear();
        //sort rules according to active comparators
        activeComparator.forEach(comparator -> {
            Collections.sort(rules, comparator);
        });

        this.getChildren().addAll(rules);

        requestLayout();
    }

    public List<RuleView> getAllRules() {
        return allRules;
    }

    public void setAllRules(List<RuleView> ar) {
        allRules = ar;
    }

    public void removeComparator(Comparator<RuleView> comp){
        activeComparator.remove(comp);
        filterRules();
    }

    public void addComparator(Comparator<RuleView> comp){
        if(!activeComparator.contains(comp)){
            activeComparator.add(comp);
            filterRules();
        }
    }

    public void removeAllComparators(){
        this.activeComparator.clear();
        filterRules();
    }


}
