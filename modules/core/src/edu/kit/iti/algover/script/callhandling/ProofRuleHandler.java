package edu.kit.iti.algover.script.callhandling;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.script.ast.CallStatement;
import edu.kit.iti.algover.script.data.GoalNode;
import edu.kit.iti.algover.script.data.State;
import edu.kit.iti.algover.script.data.Value;
import edu.kit.iti.algover.script.data.VariableAssignment;
import edu.kit.iti.algover.script.exceptions.ScriptCommandNotApplicableException;
import edu.kit.iti.algover.script.interpreter.Evaluator;
import edu.kit.iti.algover.script.interpreter.Interpreter;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuilder;

import java.math.BigInteger;
import java.util.*;

/**
 * Handler implementation for ProofRules that are implemented in Java ans implement the interface ProofRule
 *
 * To use these proof rules, they are loaded using the Java ServiceLoader.
 * @author S. Grebing
 */
public class ProofRuleHandler implements CommandHandler<ProofNode> {
    /**
     * List of all available rule objects
     */
    private List<ProofRule> rules = new ArrayList<>();

    /**
     * Map of rulename (String) to its Rule object
     */
    private Map<String, ProofRule> ruleMap = new HashMap<>();


    private ServiceLoader<ProofRule> loader;

    /**
     * Loads all rules via ServiceLoader and initializes the data structures
     */
    public ProofRuleHandler() {

        // REVIEW: Now, the project is meant to contain these rules and the DafnyRule s. -> Use project,getAllRules()
        // REVIEW: WHy is the loader retained after completion of the constructor?
        loader = ServiceLoader.load(ProofRule.class);
        loader.iterator().forEachRemaining(proofRule -> {
            rules.add(proofRule);
            ruleMap.put(proofRule.getName(), proofRule);
        });
    }

    /**
     * Loads all rules implemenetd in Java via ServiceLoader and initializes the data structures
     * The loads all rules that are passed as parameters and adds them to the datastructures.
     *
     * @param rules List of additional Proof rule objects
     */
    public ProofRuleHandler(List<ProofRule> rules) {

        loader = ServiceLoader.load(ProofRule.class);
        loader.iterator().forEachRemaining(proofRule -> {
            rules.add(proofRule);
            ruleMap.put(proofRule.getName(), proofRule);
        });

        this.rules = rules;
        rules.forEach(proofRule -> ruleMap.put(proofRule.getName(), proofRule));
    }

    /**
     * Check whether call can be handled by this object
     *
     * @param call
     * @return true if the call command could be found among the available ProofRule objects
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
        if (!ruleMap.keySet().contains(call.getCommand())) {
            throw new IllegalStateException();
        }
        //get the call command to apply and the selected goal node
        ProofRule pr = ruleMap.get(call.getCommand());
        State<ProofNode> state = interpreter.getCurrentState();
        ProofNode parent = state.getSelectedGoalNode();

        try {
            //evaluate the parameters
            Parameters ruleParams = new Parameters();
            Evaluator<ProofNode> evaluator = new Evaluator<>(params, parent);

            call.getParameters().forEach((variable, expression) -> {
                        Value val = evaluator.eval(expression);
                        ruleParams.putValue(variable.getIdentifier(), convertValuesToTypedValues(val));
                    }
            );

            //apply the rule
            ProofRuleApplication proofRuleApplication = pr.makeApplication(parent, ruleParams);

            if (proofRuleApplication.getApplicability() == ProofRuleApplication.Applicability.APPLICABLE) {

                List<ProofNode> newNodes = RuleApplicator.applyRule(proofRuleApplication, parent);

                List<ProofNode> newGoals = new ArrayList<>();

                //add new nodes to state, remove expanded node from state
                newGoals.addAll(newNodes);
                //change state depending on whether proof branch is closed or not
                if (newGoals.size() >= 1) {
                    interpreter.getCurrentState().getGoals().addAll(newGoals);
                    interpreter.getCurrentState().getGoals().remove(parent);
                    interpreter.getCurrentState().setSelectedGoalNode(interpreter.getCurrentGoals().get(0));
                } else {
                    interpreter.getCurrentState().setSelectedGoalNode(null);
                    parent.setClosed(true);
                    parent.addMutator(call);

                }

            } else {
                throw new ScriptCommandNotApplicableException(pr, call);
            }

        } catch (RuleException e) {
            throw new ScriptCommandNotApplicableException(e, pr, call);
        }


    }



    private Object convertValuesToTypedValues(Value val) {
        switch (val.getType()) {
            case STRING:
            case INT:
            case BOOL:
            case TERM:
                return val.getData();

            default:
                throw new Error("not implemented yet");
        }
    }

    @Override
    public boolean isAtomic() {
        return true;
    }
}

