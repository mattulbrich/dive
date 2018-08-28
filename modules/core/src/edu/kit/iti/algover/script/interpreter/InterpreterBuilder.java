package edu.kit.iti.algover.script.interpreter;


import edu.kit.iti.algover.proof.MethodPVCBuilder;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.script.ast.ASTNode;
import edu.kit.iti.algover.script.ast.ProofScript;
import edu.kit.iti.algover.script.callhandling.BuiltinCommands;
import edu.kit.iti.algover.script.callhandling.DefaultLookup;
import edu.kit.iti.algover.script.callhandling.ProofRuleHandler;
import edu.kit.iti.algover.script.parser.Visitor;

import java.util.ArrayList;
import java.util.Collection;

/**
 * TODO Refactor build interpreter in build and not before
 * @author S.Grebing
 *
 */

public class InterpreterBuilder {

    private final BuiltinCommands.AssertionCommand builtInAssert = new BuiltinCommands.AssertionCommand();

    private ProofRuleHandler prh = new ProofRuleHandler();

    //add other builtInCommandsHere

    /**
     * Lookup for all available rule and commandhandlers
     */
    private DefaultLookup lookup = new DefaultLookup(getBuiltInAssert(), prh);
    //entrypoint
    private ASTNode entryNode;

    public BuiltinCommands.AssertionCommand getBuiltInAssert() {
        return builtInAssert;
    }


    public ProofRuleHandler getPrh() {
        return prh;
    }
    /**

     * Interpreter
     */
    private Interpreter<ProofNode> interpreter = new Interpreter<>(lookup);

    public void setEntryPoint(ASTNode entryPoint) {
        this.entryNode = entryPoint;
    }
    /**
     * Entrypoint for interpreter
     */
    private ProofScript entryPoint;

    public DefaultLookup getLookup() {
        return lookup;
    }

    public Interpreter<ProofNode> getInterpreter() {
        return interpreter;
    }

    /**
     * Set script to start with interpretation
     *
     * @param entryPoint
     * @return
     */
    public InterpreterBuilder startWith(ASTNode entryPoint) {
        this.entryNode = entryPoint;
        return this;
    }

    /**
     * Build the interpreter
     *
     * @return Interpreter
     */
    public Interpreter<ProofNode> build() {
        return interpreter;
    }


    /**
     * Handle entry listener
     *
     * @param v
     * @return
     */
    public InterpreterBuilder onEntry(Visitor v) {
        interpreter.getEntryListeners().add(v);
        return this;
    }


    /**
     * Handle Exit Listener
     *
     * @param v
     * @return
     */
    public InterpreterBuilder onExit(Visitor v) {
        interpreter.getExitListeners().add(v);
        return this;
    }


    /**
     * Set Matcher
     *
     * @param matcher TermMatcher
     * @return
     */
    public InterpreterBuilder addMatcher(TermMatcherApi matcher) {
        interpreter.setMatcherApi(matcher);
        return this;
    }


    public InterpreterBuilder startState(ProofNode startGoal) {
        interpreter.newState(startGoal);
        return this;
    }

    public InterpreterBuilder setProofRules(Collection<ProofRule> proofRules) {
        prh = new ProofRuleHandler(new ArrayList<>(proofRules));
        lookup = new DefaultLookup(getBuiltInAssert(), this.prh);
        interpreter.setFunctionLookup(lookup);
        return this;
    }


    public InterpreterBuilder setProof(Proof proof) {
        interpreter.setCurrentProof(proof);
        return this;
    }
}
