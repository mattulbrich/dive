package edu.kit.iti.algover.script.callhandling;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.script.ast.CallStatement;
import edu.kit.iti.algover.script.data.VariableAssignment;
import edu.kit.iti.algover.script.interpreter.Interpreter;

import java.util.ArrayList;
import java.util.List;

/**
 * Created by sarah on 8/17/17.
 */
public class ProofRuleHandler implements CommandHandler<ProofNode> {
    List<ProofRule> rules = new ArrayList<>();


    public ProofRuleHandler() {
    }

    public ProofRuleHandler(List<ProofRule> rules) {
        this.rules = rules;
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
    public void evaluate(Interpreter<ProofNode> interpreter, CallStatement call, VariableAssignment params) {
        //TODO

    }

    @Override
    public boolean isAtomic() {
        return true;
    }
}

