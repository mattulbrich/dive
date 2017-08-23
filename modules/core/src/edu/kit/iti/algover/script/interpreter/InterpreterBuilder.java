package edu.kit.iti.algover.script.interpreter;


import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.script.ast.ProofScript;
import edu.kit.iti.algover.script.callhandling.DefaultLookup;
import edu.kit.iti.algover.script.data.ProofNodeData;
import edu.kit.iti.algover.script.parser.Visitor;

import java.io.IOException;
import java.util.Collection;

/**
 * @author Alexander Weigl
 * @version 1 (21.05.17)
 */

public class InterpreterBuilder {

    /**
     * Lookup for all available rule and commandhandlers
     */
    private DefaultLookup lookup = new DefaultLookup();
    /**
     * Interpreter
     */
    private Interpreter<ProofNodeData> interpreter = new Interpreter<>(lookup);
    /**
     * Entrypoint for interpreter
     */
    private ProofScript entryPoint;

    public DefaultLookup getLookup() {
        return lookup;
    }

    public Interpreter<ProofNodeData> getInterpreter() {
        return interpreter;
    }

    public ProofScript getEntryPoint() {
        return entryPoint;
    }


    /**
     * Add proof scripts that can be called and add them to proof script handler
     * @param file
     * @return
     * @throws IOException
     */
   /* public InterpreterBuilder addProofScripts(File file) throws IOException {
        return addProofScripts(Facade.getAST(file));
    }

    public InterpreterBuilder addProofScripts(List<ProofScript> ast) {
        psh.addScripts(ast);
        return this;
    }

    public InterpreterBuilder scriptSearchPath(File... paths) {
        psh.getSearchPath().addAll(Arrays.asList(paths));
        return this;
    }

    public InterpreterBuilder register(ProofScript... script) {
        psh.addScripts(Arrays.asList(script));
        return this;
    }

    */

    /**
     * Set script to start with interpretation
     *
     * @param entryPoint
     * @return
     */
    public InterpreterBuilder startWith(ProofScript entryPoint) {
        this.entryPoint = entryPoint;
        return this;
    }

    /**
     * Build the interpreter
     *
     * @return Interpreter
     */
    public Interpreter<ProofNodeData> build() {
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
/*
    public InterpreterBuilder proof(KeYEnvironment env, Proof proof) {
        this.keyEnvironment = env;
        this.proof = proof;
        return proof(new ProofApi(proof, env));
    }

    public InterpreterBuilder scriptCommands() {
        return scriptCommands(KeYApi.getScriptCommandApi().getScriptCommands());
    }

    public InterpreterBuilder scriptCommands(Collection<ProofScriptCommand> commands) {
        commands.forEach(m -> pmc.getCommands().put(m.getName(), m));
        return this;
    }



    public InterpreterBuilder addMatcher(ProofApi api) {
        ScriptApi scriptApi = api.getScriptApi();
        interpreter.setMatcherApi(new KeYMatcher(scriptApi, interpreter));
        return this;
    }





    public InterpreterBuilder captureHistory() {
        if (historyLogger == null)
            historyLogger = new HistoryListener(interpreter);
        return onEntry(historyLogger);
    }


    public InterpreterBuilder log(String prefix) {
        if (logger == null)
            logger = new ScopeLogger("interpreter");
        return onEntry(logger);
    }

    public InterpreterBuilder proof(ProofApi pa) {
        addKeyMatcher(pa);
        pa.getRules().forEach(s -> pmr.getRules().put(s, null));
        return this;
    }

    public InterpreterBuilder setScripts(List<ProofScript> scripts) {
        psh.getScripts().clear();
        return addProofScripts(scripts);
    }

    public InterpreterBuilder inheritState(Interpreter<KeyData> interpreter) {
        this.interpreter.pushState(interpreter.peekState());
        return this;
    }

    public InterpreterBuilder ignoreLines(Set<Integer> lines) {
        CommandHandler<KeyData> ignoreHandler = new CommandHandler<KeyData>() {
            @Override
            public boolean handles(CallStatement call) throws IllegalArgumentException {
                return lines.contains(call.getStartPosition().getLineNumber());
            }

            @Override
            public void evaluate(Interpreter<KeyData> interpreter, CallStatement call, VariableAssignment params) {
                //System.out.println("InterpreterBuilder.evaluate");
            }
        };
        lookup.getBuilders().add(0, ignoreHandler);
        return this;
    }

    public InterpreterBuilder ignoreLinesUntil(final int caretPosition) {
        CommandHandler<KeyData> ignoreHandler = new CommandHandler<KeyData>() {
            @Override
            public boolean handles(CallStatement call) throws IllegalArgumentException {
                return call.getRuleContext().getStart().getStartIndex() < caretPosition;
            }

            @Override
            public void evaluate(Interpreter<KeyData> interpreter, CallStatement call, VariableAssignment params) {
                System.out.println("InterpreterBuilder.evaluate");
            }
        };
        lookup.getBuilders().add(0, ignoreHandler);
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
