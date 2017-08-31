package edu.kit.iti.algover.script.callhandling;

import java.math.BigInteger;
import java.util.Map;

import edu.kit.iti.algover.script.ast.CallStatement;
import edu.kit.iti.algover.script.ast.Variable;
import edu.kit.iti.algover.script.data.GoalNode;
import edu.kit.iti.algover.script.data.State;
import edu.kit.iti.algover.script.data.Value;
import edu.kit.iti.algover.script.data.VariableAssignment;
import edu.kit.iti.algover.script.interpreter.Interpreter;
import org.junit.Assert;


/**
 * @author Alexander Weigl
 * @version 1 (21.05.17)
 */

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
            for (GoalNode<T> gn : interpreter.getCurrentGoals()) {
                System.out.format("%s %s%n  %s%n", gn == interpreter.getSelectedNode() ? "*" : " ", gn.getData(), gn.getAssignments().asMap());
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
        public void evaluate(Interpreter<String> interpreter, CallStatement call, VariableAssignment params) {
            Value<BigInteger> val = (Value<BigInteger>) params.getValues().getOrDefault(
                    new Variable("#1"),
                    Value.from(2));
            int num = val.getData().intValue();
            GoalNode<String> g = interpreter.getSelectedNode();
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

