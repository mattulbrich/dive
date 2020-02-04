/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.nuscript;

import edu.kit.iti.algover.nuscript.ast.ScriptAST.Cases;
import edu.kit.iti.algover.nuscript.ast.ScriptAST.Command;
import edu.kit.iti.algover.nuscript.ast.ScriptAST.Parameter;
import edu.kit.iti.algover.nuscript.ast.ScriptAST.Script;
import edu.kit.iti.algover.nuscript.ast.ScriptAST.Statement;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.RuleApplicator;
import edu.kit.iti.algover.rules.RuleException;

import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class Interpreter {

    private final Map<String, ProofRule> knownRules;

    private final ProofNode rootNode;

    private List<ProofNode> currentNodes;

    public Interpreter(ProofNode rootNode) {
        this.rootNode = rootNode;
        this.knownRules = makeKnownRules();
    }

    private Map<String, ProofRule> makeKnownRules() {
        Map<String, ProofRule> result = new HashMap<>();
        PVC pvc = rootNode.getPVC();
        Collection<ProofRule> allRules = pvc.getProject().getProofRules(pvc);
        for (ProofRule rule : allRules) {
            result.put(rule.getName(), rule);
        }
        return result;
    }

    public void interpret(Script script) throws ScriptException {
        currentNodes = List.of(rootNode);

        for (Statement statement : script.getStatements()) {
            statement.<Void>doCommandOrCases(this::interpretCommand, this::interpretCases);
        }
    }

    private Void interpretCases(Cases cases) {
        return null;
    }

    private Void interpretCommand(Command command) throws ScriptException {

        if(currentNodes.size() != 1) {
            throw new ScriptException("Command cannot be applied, there is more than one open goal");
        }

        ProofNode node = currentNodes.get(0);

        ProofRule rule = knownRules.get(command.getCommand().getText());
        if (rule == null) {
            throw new ScriptException();
        }

        try {
            ProofRuleApplication proofRuleApplication = rule.makeApplication(node, null);
            List<ProofNode> newNodes = RuleApplicator.applyRule(proofRuleApplication, node);
            currentNodes = newNodes;
        } catch (RuleException e) {
            throw new ScriptException(e);
        }

        return null;
    }

    private void interpretParameters(List<Parameter>) {
        
    }

}
