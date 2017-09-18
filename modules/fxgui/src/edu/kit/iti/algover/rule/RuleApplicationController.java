package edu.kit.iti.algover.rule;

import com.jfoenix.controls.JFXMasonryPane;
import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Sequent;
import javafx.scene.control.SelectionModel;
import javafx.scene.control.SingleSelectionModel;

import java.util.ArrayList;
import java.util.ServiceLoader;

public class RuleApplicationController {

    public static final double RULE_CELL_WIDTH = 100;
    public static final double RULE_CELL_HEIGHT = 60;
    public static final double SPACING = 4;

    private final JFXMasonryPane view;

    private final ArrayList<RuleView> rules;

    private final SelectionModel<RuleView> selectionModel;

    public RuleApplicationController(ProjectManager manager) {
        view = new JFXMasonryPane();
        view.setCellWidth(RULE_CELL_WIDTH);
        view.setCellHeight(RULE_CELL_HEIGHT);
        view.setVSpacing(SPACING);
        view.setHSpacing(SPACING);

        selectionModel = new RuleSelectionModel();

        rules = new ArrayList<>();

        for (ProofRule rule : ServiceLoader.load(ProofRule.class)) {
            addRule(rule);
        }
    }

    public JFXMasonryPane getView() {
        return view;
    }

    public void addRule(ProofRule rule) {
        RuleView ruleView = new RuleView(rule, selectionModel);
        rules.add(ruleView);
        view.getChildren().add(ruleView);
    }

    public void considerApplication(ProofNode target, Sequent selection, TermSelector selector) {
        rules.forEach(ruleView -> {
            ruleView.considerApplication(target, selection, selector);
        });
    }

    public void resetConsideration() {
        rules.forEach(RuleView::resetConsideration);
    }

    private class RuleSelectionModel extends SingleSelectionModel<RuleView> {
        @Override
        protected RuleView getModelItem(int i) {
            return rules.get(i);
        }

        @Override
        protected int getItemCount() {
            return rules.size();
        }
    }
}
