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
     * List of all avaiöable rule objects
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
     * @return true if the call command could be fpund among the available ProofRule objects
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
//Terms throw a class cast exception at the moment
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
            case TERM:
                //TODO build the term object from data
                return new Parameters.TypedValue(Term.class, val.getData());
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

