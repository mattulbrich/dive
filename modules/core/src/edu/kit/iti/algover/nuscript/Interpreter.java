/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.nuscript;

import edu.kit.iti.algover.nuscript.ScriptAST.ByClause;
import edu.kit.iti.algover.nuscript.ScriptAST.Case;
import edu.kit.iti.algover.nuscript.ScriptAST.Cases;
import edu.kit.iti.algover.nuscript.ScriptAST.Command;
import edu.kit.iti.algover.nuscript.ScriptAST.Parameter;
import edu.kit.iti.algover.nuscript.ScriptAST.Script;
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
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.Either;
import edu.kit.iti.algover.util.FormatException;
import edu.kit.iti.algover.util.Util;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.misc.ParseCancellationException;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * This class implements an interpreter for proof scripts.
 *
 * This has been retrofitted to be an AST visitor; hence it
 * does not fully follow the principle.
 *
 * You are probably interested in {@link #interpret(Script)}
 * or {@link #interpret(String)}.
 */
public final class Interpreter extends DefaultScriptASTVisitor<Void, Void, ScriptException> {

    /** Used for debugging */
    private static final boolean VERBOSE = false;

    /** The set of available rules for this particular proof */
    private final Map<String, ProofRule> knownRules;

    /** The freshly created proof root */
    private final ProofNode rootNode;

    /** The proof object provided to the constructor */
    private final Proof proof;

    /** The reference graph used to track references */
    private final ReferenceGraph referenceGraph;

    /** current open goals, change during interpretation */
    private List<ProofNode> currentNodes;

    /** A collection of exceptions that arise during interpretation */
    private final List<Exception> failures = new ArrayList<>();

    /**
     * Construct a new interpreter.
     *
     * @param proof the non-null proof to which the script refers.
     */
    public Interpreter(Proof proof) {
        this.referenceGraph = proof.getReferenceGraph();
        this.rootNode = ProofNode.createRoot(proof.getPVC());
        this.proof = proof;
        this.knownRules = makeKnownRules();
    }

    /**
     * Interpret the script given as argument.
     * Exceptions are taken down in {@link #failures} and are not reported here.
     *
     * @param scriptText the non-null scriptText to be interpreted
     */
    public void interpret(String scriptText) {
        try {
            Script script = Scripts.parseScript(scriptText);
            interpret(script);
        } catch (RecognitionException | ParseCancellationException rex) {
            failures.add(rex);
        }
    }

    /**
     * Interpret the script given as argument.
     * Exceptions are taken down in {@link #failures} and are not reported here.
     *
     * @param script the non-null script to be interpreted
     */
    public void interpret(Script script) {
        currentNodes = singleList(rootNode);
        try {
            script.accept(this, null);
        } catch (ScriptException e) {
            failures.add(e);
        }
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

    private Map<String, ProofRule> makeKnownRules() {
        Map<String, ProofRule> result = new HashMap<>();
        PVC pvc = rootNode.getPVC();
        Collection<ProofRule> allRules = pvc.getProject().getProofRules(pvc);
        for (ProofRule rule : allRules) {
            result.put(rule.getName(), rule);
        }
        return result;
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

    @Override
    public Void visitCases(Cases cases, Void arg) throws ScriptException {
        for (Case cas : cases.getCases()) {
            ProofNode node = findCase(cas);
            cas.setProofNode(node);
            if (node == null) {
                throw new ScriptException("Unknown label " + cas.getLabel().getText(), cas);
            }
            List<ProofNode> oldCurrent = currentNodes;
            currentNodes = singleList(node);
            cas.accept(this, null);
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

    @Override
    public Void visitCommand(Command command, Void arg) throws ScriptException {

        if (currentNodes.size() != 1) {
            ProofNode node = null;
            if (currentNodes.size() > 0) {
                // Valentin: Where is this used?
                node = currentNodes.get(0).getParent();
            }
            throw new ScriptException(
                    "Command cannot be applied, there is more than one (or no) open goal",
                    command);
        }

        ProofNode node = currentNodes.get(0);
        command.setProofNode(node);

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

            ByClause byClause = command.getByClause();
            if (byClause != null) {
                if (currentNodes.size() != 2) {
                    throw new ScriptException("by clauses are only allowed for rules with two cases", command, node);
                }
                List<ProofNode> oldCurrent = currentNodes;
                currentNodes = List.of(oldCurrent.get(0));
                byClause.accept(this, null);
                currentNodes = List.of(oldCurrent.get(1));
            }
        } catch(ScriptException e) {
            this.failures.add(e);
            currentNodes = List.of();
        } catch (Exception e) {
            ScriptException scriptEx = new ScriptException(e, command, node);
            this.failures.add(scriptEx);
            currentNodes = List.of();
        }

        return null;
    }

    private Parameters interpretParameters(ProofNode node, ProofRule rule, List<Parameter> params) throws ScriptException {
        Parameters result = new Parameters();
        Map<String, ParameterDescription<?>> knownParams = rule.getAllParameters();
        int paramCounter = 1;
        for (Parameter param : params) {
            Token nameToken = param.getName();
            String paramName;
            if(nameToken == null) {
                paramName = "#" + paramCounter;
                paramCounter ++;
            } else {
                paramName = nameToken.getText();
            }

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

            case ScriptParser.SELECTOR_LITERAL:
                try {
                    obj = new TermParameter(new TermSelector(value.getText()), node.getSequent());
                } catch (FormatException e) {
                    throw new ScriptException("Illegal selector literal", e, param, node);
                }
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
                    Either<Term, Sequent> expOrSeq = tp.parseTermOrSequent(string);
                    if (expOrSeq.isRight()) {
                        obj = new TermParameter(expOrSeq.getRight(), node.getSequent());
                    } else {
                        obj = new TermParameter(expOrSeq.getLeft(), node.getSequent());
                    }
                } catch (DafnyException | DafnyParserException e) {
                    throw new ScriptException("Cannot parse term/sequent '" + string + "'", e, param, node);
                }
                break;

            case ScriptParser.DIGITS:
                obj = Integer.valueOf(value.getText());
                break;

            default:
                throw new Error("Should not be reached: " + value);
            }

            if (!knownParam.acceptsValue(obj)) {
                throw new ScriptException("Parameter '" + paramName +
                        "' expects an argument of type " + knownParam.getType() +
                        ", cannot digest '" + obj + "'", param, node);
            }
            result.checkAndPutValue(knownParam, obj);

        }
        return result;
    }
}
