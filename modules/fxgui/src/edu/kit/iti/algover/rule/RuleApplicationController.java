package edu.kit.iti.algover.rule;

import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.prettyprint.PrettyPrint;
import javafx.geometry.Orientation;
import javafx.scene.Node;
import javafx.scene.control.SplitPane;

import java.util.ServiceLoader;

public class RuleApplicationController {

    private final SplitPane view;
    private final RuleApplicationView ruleApplicationView;

    public RuleApplicationController(ProjectManager manager) {
        ruleApplicationView = new RuleApplicationView();
        view = new SplitPane(ruleApplicationView, new ScriptView());
        view.setDividerPositions(0.7);
        view.setOrientation(Orientation.VERTICAL);

        for (ProofRule rule : ServiceLoader.load(ProofRule.class)) {
            addProofRule(rule);
        }
    }

    public Node getRuleApplicationView() {
        return view;
    }

    public void addProofRule(ProofRule rule) {
        ruleApplicationView.getRuleGrid().addRule(new RuleView(rule, ruleApplicationView.getRuleGrid().getSelectionModel()));
    }

    public void considerApplication(ProofNode target, Sequent selection, TermSelector selector) {
        try {
            Term term = selector.selectSubterm(selection);
            String prettyPrinted = new PrettyPrint().print(term, 60).toString();
            ruleApplicationView.getTermToConsider().setText(prettyPrinted);
        } catch (RuleException e) {
            e.printStackTrace();
        }
        ruleApplicationView.getRuleGrid().getRules().forEach(ruleView -> {
            ruleView.considerApplication(target, selection, selector);
        });
    }

    public void resetConsideration() {
        ruleApplicationView.getRuleGrid().getRules().forEach(RuleView::resetConsideration);
        ruleApplicationView.getTermToConsider().setText("");
    }

}
