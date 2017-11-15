package edu.kit.iti.algover.rule;

import edu.kit.iti.algover.FxmlController;
import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.prettyprint.PrettyPrint;
import javafx.fxml.FXML;
import javafx.geometry.Orientation;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.control.SplitPane;

import java.util.ServiceLoader;

public class RuleApplicationController extends FxmlController implements RuleApplicationListener {

    @FXML private Label termToConsider;
    @FXML private RuleGrid ruleGrid;
    @FXML private ScriptView scriptView;

    public RuleApplicationController() {
        super("RuleApplicationView.fxml");

        for (ProofRule rule : ServiceLoader.load(ProofRule.class)) {
            addProofRule(rule);
        }
    }

    public Node getRuleApplicationView() {
        return view;
    }

    public void addProofRule(ProofRule rule) {
        ruleGrid.addRule(new RuleView(rule, ruleGrid.getSelectionModel(), this));
    }

    public void considerApplication(ProofNode target, Sequent selection, TermSelector selector) {
        try {
            Term term = selector.selectSubterm(selection);
            String prettyPrinted = new PrettyPrint().print(term, 60).toString();
            termToConsider.setText(prettyPrinted);
        } catch (RuleException e) {
            e.printStackTrace();
        }
        ruleGrid.getRules().forEach(ruleView -> {
            ruleView.considerApplication(target, selection, selector);
        });
    }

    public void resetConsideration() {
        ruleGrid.getRules().forEach(RuleView::resetConsideration);
        termToConsider.setText("");
    }

    @Override
    public void appliedRule(ProofRuleApplication application) {
        System.out.println("Changes: " + application.getBranchInfo().get(0).getReplacements());
    }
}
