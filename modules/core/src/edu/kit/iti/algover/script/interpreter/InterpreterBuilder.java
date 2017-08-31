package edu.kit.iti.algover.script.interpreter;


import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.script.ast.ASTNode;
import edu.kit.iti.algover.script.ast.ProofScript;
import edu.kit.iti.algover.script.callhandling.BuiltinCommands;
import edu.kit.iti.algover.script.callhandling.DefaultLookup;
import edu.kit.iti.algover.script.callhandling.ProofRuleHandler;
import edu.kit.iti.algover.script.data.GoalNode;
import edu.kit.iti.algover.script.parser.Visitor;

import java.util.ArrayList;
import java.util.Collection;

/**
 * @author S.Grebing
 *
 */

public class InterpreterBuilder {

    private final BuiltinCommands.AssertionCommand builtInAssert = new BuiltinCommands.AssertionCommand();
    private ProofRuleHandler prh = new ProofRuleHandler();

    //add other builtInCommadnsHere

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
    public InterpreterBuilder addMatcher(TermMatcher matcher) {
        interpreter.setMatcherApi(matcher);
        return this;
    }

    public InterpreterBuilder rules(Collection<ProofRule> commands) {
        //commands.forEach(m -> pmc.getCommands().put(m.getName(), m));
        return this;
    }

    public InterpreterBuilder startState(GoalNode<ProofNode> startGoal) {
        interpreter.newState(startGoal);
        return this;
    }

    public InterpreterBuilder setProofRules(Collection<ProofRule> proofRules) {
        this.prh = new ProofRuleHandler(new ArrayList<>(proofRules));
        return this;
    }



/*    public InterpreterBuilder addMatcher(ProofApi api) {
        ScriptApi scriptApi = api.getScriptApi();
        interpreter.setMatcherApi(new KeYMatcher(scriptApi, interpreter));
        return this;
    }



    public InterpreterBuilder startState() {
        if (proof == null || keyEnvironment == null)
            throw new IllegalStateException("Call proof(..) before startState");

        final ProofApi pa = new ProofApi(proof, keyEnvironment);
        final ProjectedNode root = pa.getFirstOpenGoal();
        final KeyData keyData = new KeyData(root.getProofNode(), pa.getEnv(), pa.getProof());
        final GoalNode<KeyData> startGoal = new GoalNode<>(null, keyData, keyData.isClosedNode());
        return startState(startGoal);
    }

    private InterpreterBuilder startState(GoalNode<KeyData> startGoal) {
        interpreter.newState(startGoal);
        return this;
    }

 /*
      @Getter
    private final ProofScriptHandler psh = new ProofScriptHandler();
    @Getter
    private final MacroCommandHandler pmh = new MacroCommandHandler();
    @Getter
    private final RuleCommandHandler pmr = new RuleCommandHandler();
    @Getter
    private ProofScriptCommandBuilder pmc = new ProofScriptCommandBuilder();
    @Getter
    private ProofScript entryPoint;
    @Getter
    private Proof proof;
    @Getter
    private KeYEnvironment keyEnvironment;
    @Getter
    private HistoryListener historyLogger;
    @Getter
    private ScopeLogger logger;
    @Getter
    private DefaultLookup lookup = new DefaultLookup(psh, pmh, pmr, pmc);
    private Interpreter<KeyData> interpreter = new Interpreter<>(lookup);*/
}
