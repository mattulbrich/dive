package edu.kit.iti.algover.rule;

import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.script.parser.PrettyPrinter;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.prettyprint.PrettyPrint;
import javafx.scene.Node;

import java.util.ServiceLoader;

public class RuleApplicationController {

    private final RuleApplicationView view;

    public RuleApplicationController(ProjectManager manager) {
        view = new RuleApplicationView();

        for (ProofRule rule : ServiceLoader.load(ProofRule.class)) {
            addProofRule(rule);
        }
    }

    public Node getView() {
        return view;
    }

    public void addProofRule(ProofRule rule) {
        view.getRuleGrid().addRule(new RuleView(rule, view.getRuleGrid().getSelectionModel()));
    }

    public void considerApplication(ProofNode target, Sequent selection, TermSelector selector) {
        try {
            Term term = selector.selectSubterm(selection);
            String prettyPrinted = new PrettyPrint().print(term, 60).toString();
            view.getTermToConsider().setText(prettyPrinted);
        } catch (RuleException e) {
            e.printStackTrace();
        }
        view.getRuleGrid().getRules().forEach(ruleView -> {
            ruleView.considerApplication(target, selection, selector);
        });
    }

    public void resetConsideration() {
        view.getRuleGrid().getRules().forEach(RuleView::resetConsideration);
        view.getTermToConsider().setText("");
    }

}
