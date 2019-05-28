package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.references.ReferenceGraph;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.script.ast.*;
import edu.kit.iti.algover.script.exceptions.InterpreterRuntimeException;
import edu.kit.iti.algover.script.exceptions.ScriptCommandNotApplicableException;
import edu.kit.iti.algover.script.interpreter.Interpreter;
import edu.kit.iti.algover.script.interpreter.InterpreterBuilder;
import edu.kit.iti.algover.script.interpreter.TermMatcherApi;
import edu.kit.iti.algover.script.parser.DefaultASTVisitor;
import edu.kit.iti.algover.script.parser.Facade;
import edu.kit.iti.algover.util.ObservableValue;
import edu.kit.iti.algover.util.ProofTreeUtil;
import nonnull.NonNull;
import nonnull.Nullable;

import java.util.*;

/**
 * Proof Object
 * This object contains the proof root as well as the script root
 * It has to be build by the ProjectManager in order to contain a valid interpreter.
 *
 * @author Sarah Grebing
 * @author M. Ulbrich, refactoring Jan 2018
 */
public class Proof {

    public ReferenceGraph getGraph() {
        return graph;
    }

    /**
     * The reference graph for the current proof
     */
    private ReferenceGraph graph;

    /**
     * Status of proof.
     *
     * This is a value that fires notification upon change
     */
    private final ObservableValue<ProofStatus> proofStatus =
            new ObservableValue<>("ProofStatusProperty", ProofStatus.class, ProofStatus.NON_EXISTING);

    /**
     * root of logical proof, only present as soon as a proof has been conducted.
     * (Even the empty script produces a one-node prooftree.)
     *
     * if proof state is ProofState#CHANGED_SCRIPT or ProofState#NON_EXISTING, then this ought to be null.
     */
    private @Nullable ProofNode proofRoot;


    /**
     * The script text.
     *
     * mutable, can be null if no script set so far.
     * If a proofRoot is present, it results from this very script object.
     */
    private @Nullable String script;

    /**
     * The script AST
     */
    private @Nullable ProofScript scriptAST;

    /**
     * The project to which this proof belongs
     */
    private final Project project;

    /**
     * PVC for which this proof object is created
     */
    private final PVC pvc;

    /**
     * The exception with which interpretation has failed.
     */
    /*@ invariant failException != null <==> poofStatus.getValue() == FAIL; */
    private Exception failException;

    public DafnyFile getDfyFile() {
        return dfyFile;
    }

    public void setDfyFile(DafnyFile dfyFile) {
        this.dfyFile = dfyFile;
    }

    /**
     * DafnyFile for this proof. Needed for ReferenceGraph. Is allowed to be null for downwards compatibility
     */
    private @Nullable DafnyFile dfyFile;

    public Proof(@NonNull Project project, @NonNull PVC pvc) {
        this.project = project;
        this.pvc = pvc;
    }


    public Proof(@NonNull Project project, @NonNull PVC pvc, @NonNull DafnyFile dfyFile ) {
        this.project = project;
        this.pvc = pvc;
        this.dfyFile = dfyFile;
        this.graph = new ReferenceGraph();
        this.graph.addFromReferenceMap(dfyFile, pvc.getReferenceMap());
    }

    public @NonNull Project getProject() {
        return project;
    }

    public @NonNull  PVC getPVC() {
        return pvc;
    }

    public @Nullable ProofNode getProofRoot() {
        return proofRoot;
    }

    public String getPVCName() {
        return pvc.getIdentifier();
    }

    public ProofStatus getProofStatus() {
        return proofStatus.getValue();
    }

    public Exception getFailException() {
        return failException;
    }

    public void addProofStatusListener(ObservableValue.ChangeListener<ProofStatus> listener) {
        proofStatus.addObserver(listener);
    }

    public String getScript() {
        return script;
    }

    /**
     * Parses a script as string representation and sets the parsed AST
     *
     * @param script string representation of script
     */
    public void setScriptText(String script) {
        if (this.getScript() != null) {
            saveOldDataStructures();
        }

        this.script = script;

        this.proofStatus.setValue(ProofStatus.CHANGED_SCRIPT);
    }

    /**
     * Interpret Script. A script must have been set previously.
     *
     * This will also parse the previously set script text. After this
     * {@link #getProofScript()} will return a valid script, if parsing is successful.
     */
    public void interpretScript() throws InterpreterRuntimeException, ScriptCommandNotApplicableException {
        assert script != null;

        ProofNode newRoot = ProofNode.createRoot(pvc);

        try {
            // TODO Exception handling
            this.scriptAST = Facade.getAST(script);
            //save old root
            ProofNode oldRoot = getProofRoot();

            Interpreter<ProofNode> interpreter = buildIndividualInterpreter();

            // Caution: Keep this pure constructor call, it performs the computation!
            new ProofNodeInterpreterManager(interpreter);
            interpreter.newState(newRoot);
            this.proofRoot = newRoot;

            scriptAST.getBody().forEach(interpreter::interpret);
            this.failException = null;
            proofStatus.setValue(newRoot.allLeavesClosed() ? ProofStatus.CLOSED : ProofStatus.OPEN);

        } catch (ScriptCommandNotApplicableException snap) {
            this.proofRoot = newRoot;
            this.failException = snap;
            proofStatus.setValue(ProofStatus.FAILING);
        } catch (InterpreterRuntimeException ire) {
            this.proofRoot = newRoot;
            this.failException = ire;
            proofStatus.setValue(ProofStatus.FAILING);
;

        } catch(Exception ex) {
            // publish the proof root even if the proof has (partially) failed.
            this.proofRoot = newRoot;
            this.failException = ex;

            // TODO proof state handling.
            proofStatus.setValue(ProofStatus.FAILING);
        }


    }


    // REVIEW: Review after repairing generics elsewhere
    @SuppressWarnings({"unchecked", "rawtypes"})
    private Interpreter<ProofNode> buildIndividualInterpreter() {

        InterpreterBuilder ib = new InterpreterBuilder();
        Interpreter<ProofNode> i = ib
                .setProofRules(this.project.getAllProofRules())
                .startState(getProofRoot())
                .addMatcher(new TermMatcherApi())
                .setProof(this)
                .build();

        return i;
    }

    /**
     * Set a new script, parse it and interpret it.
     *
     * <p>Convenience method for
     * <pre>
     *     setScriptText(scriptText);
     *     interpretScript();
     * </pre>
     *
     * @param scriptText
     * @return this object
     */
    public Proof setScriptTextAndInterpret(String scriptText) {
        setScriptText(scriptText);
        interpretScript();
        if(this.getGraph() != null){
            graph.toString();
        }
        return this;
    }


    /**
     * Returns a string representation of the proof tree
     *
     * @return
     */
    public String proofToString() {
        StringBuilder sb = new StringBuilder("Proof for " + this.pvc.getIdentifier() + "\n");
        if (this.getProofRoot() != null) {
            sb.append(ProofTreeUtil.toStringTree(getProofRoot()));
        } else {
            sb.append("<null> proof");
        }
        return sb.toString();
    }

    /**
     * @return an instance encapsulating the script AST.
     *         Is null as long as {@link #interpretScript()} has not yet been called validly.
     */
    public ProofScript getProofScript() {
        return scriptAST;
    }

    /**
     * This method invalidates this proof object, sets the status to dirty
     */
    public void invalidate() {
        this.proofStatus.setValue(ProofStatus.DIRTY);
    }

    /**
     * Save the old script and the old proof for comparison when reloading
     */
    private void saveOldDataStructures() {
        // future ...
    }
}

/**
 * Class handling the creation of the proof tree when interpreting script.
 * EntryListeners are informed when entering an ASTNode in the Interpreter
 * ExitsListeners are informed at then end of ASTNodes
 * Book keeping is done in this visitor
 */
class ProofNodeInterpreterManager {
    final Interpreter<ProofNode> interpreter;
    private ProofNode lastSelectedGoalNode;


    private ReferenceGraph graph;
    /**
     * The proofNodeInterpreterManager adds an entry and an exit listner to the interpreter to listen what event happen
     * during AST-Node visiting
     *
     * @param interpreter
     */
    public ProofNodeInterpreterManager(Interpreter<ProofNode> interpreter) {
        this.interpreter = interpreter;
        interpreter.getExitListeners().add(new ExitListener());
        interpreter.getEntryListeners().add(new EntryListener());
        this.graph = interpreter.getCurrentProof().getGraph();
    }

    /**
     * Access the current ReferenceGraph
     * @return
     */
    public ReferenceGraph getGraph() {
        return graph;
    }

    private class EntryListener extends DefaultASTVisitor<Void> {
        @Override
        public Void visit(Statements statements) {
            return null;
        }

        @Override
        public Void defaultVisit(ASTNode node) {
            lastSelectedGoalNode = interpreter.getSelectedNode();
            return null;
        }

        @Override
        public Void visit(AssignmentStatement assignment) {
            return defaultVisit(assignment);
            /*if(lastSelectedGoalNode == null )
                return defaultVisit(assignment);
            return null;*/
        }

        @Override
        public Void visit(SimpleCaseStatement simpleCaseStatement) {
            return null;
        }

        @Override
        public Void visit(MatchExpression matchExpression) {
            return null;
        }

        @Override
        public Void visit(Signature signature) {
            return null;
        }

        @Override
        public Void visit(Parameters parameters) {
            return null;
        }

        @Override
        public Void visit(IntegerLiteral integer) {
            return null;
        }

        @Override
        public Void visit(BinaryExpression binaryExpression) {
            return null;
        }

        @Override
        public Void visit(TermLiteral termLiteral) {
            return null;
        }

        @Override
        public Void visit(SequentLiteral sequentLiteral) {
            return null;
        }

        @Override
        public Void visit(StringLiteral stringLiteral) {
            return null;
        }

        @Override
        public Void visit(Variable variable) {
            return null;
        }

        @Override
        public Void visit(BooleanLiteral booleanLiteral) {
            return null;
        }
    }

    private class ExitListener extends DefaultASTVisitor<Void> {
        @Override
        public Void visit(SimpleCaseStatement simpleCaseStatement) {
            return null;
        }

        @Override
        public Void visit(MatchExpression matchExpression) {
            return null;
        }

        @Override
        public Void visit(Signature signature) {
            return null;
        }

        @Override
        public Void visit(Parameters parameters) {
            return null;
        }

        @Override
        public Void defaultVisit(ASTNode node) {
            lastSelectedGoalNode.setChildren(new ArrayList<>());

            List<ProofNode> goals = interpreter.getCurrentState().getGoals();

            if (goals.size() == 1 && goals.get(0).equals(lastSelectedGoalNode)) {
                if(graph != null) {
                    try {
                        graph.addFromRuleApplication(interpreter.getCurrentProof(), lastSelectedGoalNode, lastSelectedGoalNode.getChildren());
                        graph.addFromScriptNode(node,  lastSelectedGoalNode, interpreter.getCurrentProof());
                    } catch (RuleException e) {
                        throw new RuntimeException(e);
                    }
                }
                return null;
            }
            //goal list is empty, we have reached a proof
            if (goals.isEmpty()) {
                lastSelectedGoalNode.setClosed(true);
               // System.out.println("Goalist goals.size() = " + goals.size() + "is empty we have reached a full proof");
            }
            //we have newly created goals, for each of them, add them to the proofnode structure as children
            //TODO we now have a nested structure, how to add this structure to the proof tree
            if (goals.size() > 0) {
                for (ProofNode goal : goals) {
                    //we don't have a nested structure
                    if(goal.getParent() == lastSelectedGoalNode) {
                        lastSelectedGoalNode.getChildren().add(goal);
                        if(graph != null) {
                            try {
                                graph.addFromRuleApplication(interpreter.getCurrentProof(), lastSelectedGoalNode, lastSelectedGoalNode.getChildren());
                                graph.addFromScriptNode(node,  lastSelectedGoalNode, interpreter.getCurrentProof());
                            } catch (RuleException e) {
                                throw new RuntimeException(e);
                            }
                        }
                    } else {
                        //TODO handle nested structure -> maybe this is not wanted
                        ProofNode temporaryGoal = goal;
                        while(temporaryGoal.getParent() != lastSelectedGoalNode){
                            try {
                                graph.addFromRuleApplication(interpreter.getCurrentProof(), temporaryGoal, temporaryGoal.getParent().getChildren());
                                graph.addFromScriptNode(node, lastSelectedGoalNode, interpreter.getCurrentProof());
                            } catch (RuleException e) {
                                e.printStackTrace();
                            }
                            temporaryGoal = temporaryGoal.getParent();
                        }
                        lastSelectedGoalNode.getChildren().add(temporaryGoal);

                    }

                }
            }

            lastSelectedGoalNode.addMutator(node);

            return null;
        }

        @Override
        public Void visit(Statements statements) {
            return null;
        }


        /**
         * When exiting an Assignment statement a new node has to be added, because assignments change the state as well
         *
         * @param assignment
         * @return
         */
        @Override
        public Void visit(AssignmentStatement assignment) {
            lastSelectedGoalNode.setChildren(new ArrayList<>());

            List<ProofNode> goals = interpreter.getCurrentState().getGoals();

            if (goals.size() == 1 && goals.get(0).equals(lastSelectedGoalNode)) {
                return null;
            }
            if (goals.isEmpty()) {
                lastSelectedGoalNode.setClosed(true);
                // System.out.println("Goalist goals.size() = " + goals.size() + "is empty we have reached a full proof");
            }
            if (goals.size() > 0) {
                for (ProofNode goal : goals) {
                    lastSelectedGoalNode.getChildren().add(goal);
                    //TODO implement new method allowing to create "self-references"
                   /* if(graph != null) {
                        try {
                            graph.addReference(interpreter.getCurrentProof(), lastSelectedGoalNode, lastSelectedGoalNode.getChildren());
                        } catch (RuleException e) {
                            throw new RuntimeException(e);
                        }
                    }*/

                }
            }

            lastSelectedGoalNode.addMutator(assignment);

            return null;


         /*   LinkedList<ProofNode> singleChild = new LinkedList<>();
            List<ProofNode> goals = interpreter.getCurrentState().getGoals();


            if (goals.size() == 1) {
                //singleChild.add(goals.get(0).getData());
                ProofNode pn = new ProofNode(lastSelectedGoalNode,
                        null,
                        lastSelectedGoalNode.getHistory(),
                        goals.get(0).getSequent(), lastSelectedGoalNode.getRootPVC());
                pn.setVariableAssignments(lastSelectedGoalNode.getVariableAssignments().deepCopy());

                goals.get(0).addMutator(assignment);
                singleChild.add(goals.get(0));
            }
            lastSelectedGoalNode.setChildren(singleChild);
            //lastSelectedGoalNode.addMutator(assignment);
            return null;*/
//            return defaultVisit(assignment);
        }

        @Override
        public Void visit(CasesStatement casesStatement) {

            return null;
        }

        @Override
        public Void visit(CaseStatement caseStatement) {
            return null;
        }

        @Override
        public Void visit(IsClosableCase isClosableCase) {
            return null;
        }



        @Override
        public Void visit(IntegerLiteral integer) {
            return null;
        }

        @Override
        public Void visit(BinaryExpression binaryExpression) {
            return null;
        }

        @Override
        public Void visit(TermLiteral termLiteral) {
            return null;
        }

        @Override
        public Void visit(SequentLiteral sequentLiteral) {
            return null;
        }

        @Override
        public Void visit(StringLiteral stringLiteral) {
            return null;
        }

        @Override
        public Void visit(Variable variable) {
            return null;
        }

        @Override
        public Void visit(BooleanLiteral booleanLiteral) {
            return null;
        }
    }
}
