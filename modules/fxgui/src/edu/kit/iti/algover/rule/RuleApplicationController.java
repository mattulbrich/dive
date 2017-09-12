package edu.kit.iti.algover.rule;

import com.jfoenix.controls.JFXMasonryPane;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.rules.impl.TrivialAndRight;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;

import java.util.ArrayList;
import java.util.ServiceLoader;

public class RuleApplicationController {

    public static final double RULE_CELL_WIDTH = 100;
    public static final double RULE_CELL_HEIGHT = 60;
    public static final double SPACING = 4;

    private final JFXMasonryPane view;

    private final ArrayList<RuleView> rules;

    public RuleApplicationController(ProjectManager manager) {
        view = new JFXMasonryPane();
        view.setCellWidth(RULE_CELL_WIDTH);
        view.setCellHeight(RULE_CELL_HEIGHT);
        view.setVSpacing(SPACING);
        view.setHSpacing(SPACING);

        rules = new ArrayList<>();

        for (ProofRule rule : ServiceLoader.load(ProofRule.class)) {
            addRule(rule);
        }
    }

    public JFXMasonryPane getView() {
        return view;
    }

    public void addRule(ProofRule rule) {
        RuleView ruleView = new RuleView(rule);
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
}
