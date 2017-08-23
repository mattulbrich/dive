package edu.kit.iti.algover.script.callhandling;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.script.ast.CallStatement;
import edu.kit.iti.algover.script.data.VariableAssignment;
import edu.kit.iti.algover.script.exceptions.ScriptCommandNotApplicableException;
import edu.kit.iti.algover.script.interpreter.Interpreter;

import java.util.HashMap;
import java.util.Map;

/**
 * Created by sarah on 8/17/17.
 */
public class RuleCommandHandler implements CommandHandler<ProofNode> {

    private final Map<String, ProofRule> rules;

    public RuleCommandHandler() {
        this(new HashMap<>());
    }

    public RuleCommandHandler(Map<String, ProofRule> rules) {
        this.rules = rules;
    }

    @Override
    public boolean handles(CallStatement call) throws IllegalArgumentException {
        return rules.containsKey(call.getCommand());
    }

    @Override
    public void evaluate(Interpreter<ProofNode> interpreter,
                         CallStatement call,
                         VariableAssignment params) throws IllegalStateException, RuntimeException, ScriptCommandNotApplicableException {
        if (!rules.containsKey(call.getCommand())) {
            throw new IllegalStateException();
        }

        /*RuleCommand c = new RuleCommand();
        State<KeyData> state = interpreter.getCurrentState();
        GoalNode<KeyData> expandedNode = state.getSelectedGoalNode();
        KeyData kd = expandedNode.getData();
        Map<String, String> map = new HashMap<>();
        params.asMap().forEach((k, v) -> map.put(k.getIdentifier(), v.getData().toString()));
        System.out.println(map);
        try {
            map.put("#2", call.getCommand());
            EngineState estate = new EngineState(kd.getProof());
            estate.setGoal(kd.getNode());
            RuleCommand.Parameters cc = c.evaluateArguments(estate, map);
            AbstractUserInterfaceControl uiControl = new DefaultUserInterfaceControl();
            c.execute(uiControl, cc, estate);

            ImmutableList<Goal> ngoals = kd.getProof().getSubtreeGoals(kd.getNode());
            state.getGoals().remove(expandedNode);
            for (Goal g : ngoals) {
                KeyData kdn = new KeyData(kd, g.node());
                state.getGoals().add(new GoalNode<>(expandedNode, kdn, kdn.getNode().isClosed()));
            }
        } catch (Exception e) {
            if (e.getClass().equals(ScriptException.class)) {
                throw new ScriptCommandNotApplicableException(e, c, map);

            } else {
                throw new RuntimeException(e);
            }
        }
        */
    }


}
