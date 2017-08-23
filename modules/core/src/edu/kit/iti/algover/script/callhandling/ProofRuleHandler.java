package edu.kit.iti.algover.script.callhandling;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.Parameters;
import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.script.ast.CallStatement;
import edu.kit.iti.algover.script.ast.Expression;
import edu.kit.iti.algover.script.data.GoalNode;
import edu.kit.iti.algover.script.data.State;
import edu.kit.iti.algover.script.data.VariableAssignment;
import edu.kit.iti.algover.script.exceptions.ScriptCommandNotApplicableException;
import edu.kit.iti.algover.script.interpreter.Interpreter;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Handler for ProofRules
 *
 * @author S. Grebing
 */
public class ProofRuleHandler implements CommandHandler<ProofNode> {
    private List<ProofRule> rules = new ArrayList<>();
    private Map<String, ProofRule> ruleMap = new HashMap<>();


    public ProofRuleHandler() {
    }

    public ProofRuleHandler(List<ProofRule> rules) {

        this.rules = rules;
        rules.forEach(proofRule -> ruleMap.put(proofRule.getName(), proofRule));
    }

    @Override
    public boolean handles(CallStatement call) throws IllegalArgumentException {
        for (ProofRule pr : rules)
            if (pr.getName().equals(call.getCommand())) {
                return true;
            }
        return false;
    }

    @Override
    public void evaluate(Interpreter<ProofNode> interpreter, CallStatement call, VariableAssignment params) throws IllegalStateException, ScriptCommandNotApplicableException {
        if (!rules.contains(call.getCommand())) {
            throw new IllegalStateException();
        }
        ProofRule pr = ruleMap.get(call.getCommand());
        State<ProofNode> state = interpreter.getCurrentState();
        GoalNode<ProofNode> pn = state.getSelectedGoalNode();

        try {
            Parameters ruleParams = new Parameters();
            call.getParameters().forEach((variable, expression) -> System.out.println(variable.getIdentifier() + expression));
            ProofRuleApplication proofRuleApplication = pr.makeApplication(pn.getData(), ruleParams);
            if (proofRuleApplication.getApplicability().equals(ProofRuleApplication.Applicability.APPLICABLE)) {
                //TODO how do I get the applications results?
            }

        } catch (RuleException e) {
            throw new ScriptCommandNotApplicableException(e);
        }

        //TODO

    }

    @Override
    public boolean isAtomic() {
        return true;
    }
}

