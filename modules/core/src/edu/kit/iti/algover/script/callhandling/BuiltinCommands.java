package edu.kit.iti.algover.script.callhandling;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.script.ast.CallStatement;
import edu.kit.iti.algover.script.ast.Variable;
import edu.kit.iti.algover.script.data.GoalNode;
import edu.kit.iti.algover.script.data.State;
import edu.kit.iti.algover.script.data.Value;
import edu.kit.iti.algover.script.data.VariableAssignment;
import edu.kit.iti.algover.script.interpreter.Interpreter;
import edu.kit.iti.algover.term.Term;
import org.junit.Assert;


/**
 * @author Alexander Weigl
 * @version 1 (21.05.17)
 */


// REVIEW: Add the missing generic parameters! Please!

@SuppressWarnings({"unchecked", "rawtypes"})
public abstract class BuiltinCommands {
    public static abstract class BuiltinCommand<T> implements CommandHandler<T> {

        private final String name;

        protected BuiltinCommand(String name) {
            this.name = name;
        }

        public String getName() {
            return name;
        }

        @Override
        public boolean handles(CallStatement call) throws IllegalArgumentException {
            return name.equals(call.getCommand());
        }
    }

    public static class PrintCommand<T extends Object> extends BuiltinCommand<T> {
        public PrintCommand() {
            super("print_state");
        }

        @Override
        public void evaluate(Interpreter<T> interpreter, CallStatement call, VariableAssignment params) {
            for (ProofNode gn : interpreter.getCurrentGoals()) {
                System.out.format("%s %s%n  %s%n", gn == interpreter.getSelectedNode() ? "*" : " ", gn, gn.getAssignments().asMap());
            }
        }
    }

    public static class SplitCommand extends BuiltinCommand<String> {

        public SplitCommand() {
            super("split");
        }

        /**
         * Created by sarah on 5/17/17.
         */
        @Override
        @SuppressWarnings("unchecked")
        public void evaluate(Interpreter<String> interpreter, CallStatement call, VariableAssignment params) {
            // REVIEW: It seems that this cast may very easy fail if the type of "#1" is not a number!
            Value<BigInteger> val = (Value<BigInteger>) params.getValues().getOrDefault(
                    new Variable("#1"),
                    Value.from(2));
            int num = val.getData().intValue();
            ProofNode g = interpreter.getSelectedNode();
            State<String> s = interpreter.getCurrentState();
            State<String> state = new State<>(s.getGoals(), null);
            state.getGoals().remove(s.getSelectedGoalNode());
            for (char i = 0; i < num; i++) {
                //state.getGoals().add(new GoalNode<>(g, g.getData() + "." + (char) ('a' + i), g.isClosed()));
            }
            interpreter.pushState(state);
        }
    }

    /**
     * Built In Command assert
     *
     * @author A.Weigl
     * @author S. Grebing
     */
    public static class AssertionCommand extends BuiltinCommands.BuiltinCommand {

        public AssertionCommand() {
            super("assert");
        }


        @Override
        public void evaluate(Interpreter interpreter, CallStatement call, VariableAssignment params) {
            Map<Variable, Value> m = params.asMap();
            if (params.isEmpty()) {

            }
            System.out.println("Not implemented yet");

            //Value<Boolean> exp = get(m, "val", "#1");
            //Value<String> msg = get(m, "msg", "#2");
            //if (msg == null)
            //    Assert.assertTrue(exp.getData());
            //else
            //    Assert.assertTrue(msg.getData(), exp.getData());
        }
    }
}

/* if (!ruleMap.keySet().contains(call.getCommand())) {
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
        }*/
