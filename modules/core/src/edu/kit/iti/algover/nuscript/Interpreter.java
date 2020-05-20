/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.nuscript;

import edu.kit.iti.algover.nuscript.ast.ScriptAST.Case;
import edu.kit.iti.algover.nuscript.ast.ScriptAST.Cases;
import edu.kit.iti.algover.nuscript.ast.ScriptAST.Command;
import edu.kit.iti.algover.nuscript.ast.ScriptAST.Parameter;
import edu.kit.iti.algover.nuscript.ast.ScriptAST.Script;
import edu.kit.iti.algover.nuscript.parser.ScriptParser;
import edu.kit.iti.algover.nuscript.parser.Scripts;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.references.ReferenceGraph;
import edu.kit.iti.algover.rules.ParameterDescription;
import edu.kit.iti.algover.rules.Parameters;
import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.ProofRuleApplication.Applicability;
import edu.kit.iti.algover.rules.RuleApplicator;
import edu.kit.iti.algover.rules.TermParameter;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.Util;
import org.antlr.v4.runtime.Token;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class Interpreter {

    private static final boolean VERBOSE = false;

    private final Map<String, ProofRule> knownRules;
    private final ProofNode rootNode;
    private final Proof proof;
    private final ReferenceGraph referenceGraph;

    private List<ProofNode> currentNodes;

    private final List<Exception> failures = new ArrayList<>();

    public Interpreter(Proof proof) {
        this.referenceGraph = proof.getReferenceGraph();
        this.rootNode = ProofNode.createRoot(proof.getPVC());
        this.proof = proof;
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

    public void interpret(Script script) {
        currentNodes = singleList(rootNode);
        try {
            script.visit(this::interpretCommand, this::interpretCases);
        } catch (ScriptException e) {
            if (VERBOSE) {
                e.printStackTrace();
            }
            // This exception has been thrown to indicate an error during execution.
            // It has been taken down and added to the corresponding proof node.
        }
    }

    /**
     * Returns a modifiable singleton list.
     *
     * @param e a single value that will be in the list
     * @return a freshly created list that only contains e
     */
    private static <E> List<E> singleList(E e) {
        List<E> result = new ArrayList<>();
        result.add(e);
        return result;
    }

    private Void interpretCases(Cases cases) throws ScriptException {
        for (Case cas : cases.getCases()) {
            ProofNode node = findCase(cas);
            if (node == null) {
                throw new ScriptException("Unknown label \"" + cas.getLabel().getText() + "\"", cas, node);
            }
            List<ProofNode> oldCurrent = currentNodes;
            currentNodes = singleList(node);
            cas.visit(this::interpretCommand, this::interpretCases);
            currentNodes = oldCurrent;
            currentNodes.remove(node);
        }
        return null;
    }

    private ProofNode findCase(Case cas) {
        String label = Util.stripQuotes(cas.getLabel().getText());
        for (ProofNode node : currentNodes) {
            if (node.getLabel().equals(label)) {
                return node;
            }
        }
        return null;
    }

    private Void interpretCommand(Command command) throws ScriptException {

        if (currentNodes.size() != 1) {
            ProofNode node = null;
            if (currentNodes.size() > 0) {
                node = currentNodes.get(0).getParent();
            }
            throw new ScriptException(
                    "Command cannot be applied, there is more than one (or no) open goal",
                    command, node);
        }

        ProofNode node = currentNodes.get(0);

        String commandName = command.getCommand().getText();
        ProofRule rule = knownRules.get(commandName);

        try {
            if (rule == null) {
                throw new ScriptException("Unknown script command " + commandName, command, node);
            }
            Parameters params = interpretParameters(node, rule, command.getParameters());
            ProofRuleApplication proofRuleApplication = rule.makeApplication(node, params);
            proofRuleApplication = proofRuleApplication.refine();
            if(proofRuleApplication.getApplicability() != Applicability.APPLICABLE) {
                throw new ScriptException("This command is not applicable", command, node);
            }
            List<ProofNode> newNodes = RuleApplicator.applyRule(proofRuleApplication, command, node);
            node.setChildren(newNodes);
            currentNodes = newNodes;

        } catch (Exception e) {
            this.failures.add(e);
            currentNodes = List.of();
        }

        return null;
    }

    private Parameters interpretParameters(ProofNode node, ProofRule rule, List<Parameter> params) throws ScriptException {
        Parameters result = new Parameters();
        Map<String, ParameterDescription<?>> knownParams = rule.getAllParameters();
        for (Parameter param : params) {

            String paramName = param.getName().getText();
            ParameterDescription<?> knownParam = knownParams.get(paramName);

            if (knownParam == null) {
                throw new ScriptException("Unknown parameter " + paramName, param, node);
            }

            Token value = param.getValue();
            Object obj;
            switch (value.getType()) {
            case ScriptParser.STRING_LITERAL:
                obj = Util.stripQuotes(value.getText());
                break;

            case ScriptParser.FALSE:
            case ScriptParser.TRUE:
                obj = Boolean.valueOf(value.getText());
                break;

            case ScriptParser.TERM_LITERAL:
                String string = Util.stripQuotes(value.getText());

                try {
                    TermParser tp = new TermParser(node.getAllSymbols());
                    tp.setSchemaMode(true);
                    // TODO this may actually be rather naive ...
                    if (string.contains("|-")) {
                        Sequent seq = tp.parseSequent(string);
                        obj = new TermParameter(seq, node.getSequent());
                    } else {
                        Term term = tp.parse(string);
                        obj = new TermParameter(term, node.getSequent());
                    }
                } catch (DafnyException | DafnyParserException e) {
                    throw new ScriptException("Cannot parse term/sequent " + string, e, param, node);
                }
                break;

            case ScriptParser.DIGITS:
                obj = Integer.valueOf(value.getText());
                break;

            default:
                throw new Error("Should not be reached: " + value);
            }

            if (!knownParam.acceptsValue(obj)) {
                throw new ScriptException("Parameter " + paramName +
                        " expects an argument of type " + knownParam.getType() +
                        ", not " + obj, param, node);
            }
            result.checkAndPutValue(knownParam, obj);

        }
        return result;
    }

    public void interpret(String scriptText) throws ScriptException {
        Script script = Scripts.parseScript(scriptText);
        interpret(script);
    }

    public ProofNode getRootNode() {
        return rootNode;
    }

    public boolean hasFailure() {
        return !failures.isEmpty();
    }

    public List<Exception> getFailures() {
        return failures;
    }
}
