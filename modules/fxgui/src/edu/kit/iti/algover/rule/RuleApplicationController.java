package edu.kit.iti.algover.rule;

import edu.kit.iti.algover.FxmlController;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.rule.script.ScriptController;
import edu.kit.iti.algover.rule.script.ScriptView;
import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.prettyprint.PrettyPrint;
import javafx.beans.value.ObservableValue;
import javafx.fxml.FXML;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.control.SplitPane;
import org.fxmisc.flowless.VirtualizedScrollPane;

import java.util.ServiceLoader;
import java.util.concurrent.ExecutorService;
import java.util.function.Consumer;

public class RuleApplicationController extends FxmlController {

    @FXML private SplitPane splitPane;
    @FXML private Label termToConsider;
    @FXML private RuleGrid ruleGrid;

    private final ScriptView scriptView;

    private final RuleApplicationListener listener;

    private final ScriptController scriptController;

    public RuleApplicationController(ExecutorService executor, RuleApplicationListener listener) {
        super("RuleApplicationView.fxml");
        this.listener = listener;
        this.scriptController = new ScriptController(executor, listener);
        this.scriptView = scriptController.getView();

        for (ProofRule rule : ServiceLoader.load(ProofRule.class)) {
            addProofRule(rule);
        }

        ruleGrid.getSelectionModel().selectedItemProperty().addListener(this::onSelectedItemChanged);
        splitPane.getItems().add(new VirtualizedScrollPane<>(scriptView));
    }

    public void addProofRule(ProofRule rule) {
        ruleGrid.addRule(new RuleView(rule, ruleGrid.getSelectionModel(), listener));
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

    public void applyRule(ProofRuleApplication application) {
        scriptView.insertText(scriptView.getLength(), application.getScriptTranscript() + "\n");
    }

    private void onSelectedItemChanged(ObservableValue<? extends RuleView> obs, RuleView before, RuleView selected) {
        if (selected == null) {
            listener.onResetRuleApplicationPreview();
        }
    }

    public Node getRuleApplicationView() {
        return view;
    }

    public RuleGrid getRuleGrid() {
        return ruleGrid;
    }

    public ScriptView getScriptView() {
        return scriptView;
    }

    public ScriptController getScriptController() {
        return scriptController;
    }
}
