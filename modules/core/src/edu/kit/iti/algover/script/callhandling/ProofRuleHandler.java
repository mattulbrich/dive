package edu.kit.iti.algover.script.callhandling;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.script.ast.CallStatement;
import edu.kit.iti.algover.script.ast.Expression;
import edu.kit.iti.algover.script.data.GoalNode;
import edu.kit.iti.algover.script.data.State;
import edu.kit.iti.algover.script.data.Value;
import edu.kit.iti.algover.script.data.VariableAssignment;
import edu.kit.iti.algover.script.exceptions.ScriptCommandNotApplicableException;
import edu.kit.iti.algover.script.interpreter.Evaluator;
import edu.kit.iti.algover.script.interpreter.Interpreter;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;
import jdk.nashorn.internal.codegen.types.Type;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

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

    /**
     * Check whether call can be handled by this object
     *
     * @param call
     * @return
     * @throws IllegalArgumentException
     */
    @Override
    public boolean handles(CallStatement call) throws IllegalArgumentException {
        for (ProofRule pr : rules)
            if (pr.getName().equals(call.getCommand())) {
                return true;
            }
        return false;
    }

    /**
     * Apply a rule to the proof node of the current interpreter state
     * @param interpreter
     * @param call
     * @param params
     * @throws IllegalStateException
     * @throws ScriptCommandNotApplicableException
     */
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

            Evaluator<ProofNode> evaluator = new Evaluator<>(params, pn);
            call.getParameters().forEach((variable, expression) -> {
                        Value val = evaluator.eval(expression);
                        ruleParams.putValue(variable.getIdentifier(), convertValuesToTypedValues(val));
                    }
            );

            ProofRuleApplication proofRuleApplication = pr.makeApplication(pn.getData(), ruleParams);
            if (proofRuleApplication.getApplicability().equals(ProofRuleApplication.Applicability.APPLICABLE)) {
                List<ProofNode> newNodes = RuleApplicator.applyRule(proofRuleApplication, pn.getData());

                state.getGoals().remove(pn);
                //state.getGoals().add(newCreatedGoals);
                //newcreatedgoals must be goalnode<ProofNode>
            } else {
                System.out.println("Warning command not applicable");
            }

        } catch (RuleException e) {
            throw new ScriptCommandNotApplicableException(e);
        }


    }



    private Parameters.TypedValue convertValuesToTypedValues(Value val) {
        switch (val.getType()) {
            case STRING:
                return new Parameters.TypedValue(String.class, val.getData());
            case INT:
                return new Parameters.TypedValue(BigInteger.class, val.getData());
            default:
                System.out.println("Not implemented yet");
                return null;

        }
    }

    @Override
    public boolean isAtomic() {
        return true;
    }
}

