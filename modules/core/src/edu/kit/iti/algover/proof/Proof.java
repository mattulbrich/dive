/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.nuscript.Interpreter;
import edu.kit.iti.algover.nuscript.ast.ScriptAST.Script;
import edu.kit.iti.algover.nuscript.parser.Scripts;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.references.ReferenceGraph;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.util.ObservableValue;
import edu.kit.iti.algover.util.ProofTreeUtil;
import nonnull.NonNull;
import nonnull.Nullable;

import java.util.Deque;
import java.util.LinkedList;

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
     * The AST of the script
     */
    private @Nullable Script scriptAST;

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

    /**
     * DafnyFile for this proof. Needed for ReferenceGraph. Is allowed to be null for downwards compatibility
     */
    private @Nullable DafnyFile dfyFile;

    @Deprecated // get rid of this
    public Proof(@NonNull Project project, @NonNull PVC pvc) {
        this(project, pvc, null);
    }

    public Proof(@NonNull Project project, @NonNull PVC pvc, @NonNull DafnyFile dfyFile) {
        this.project = project;
        this.pvc = pvc;
        this.dfyFile = dfyFile;
        this.graph = new ReferenceGraph();
        if (dfyFile != null) {
            this.graph.addFromReferenceMap(dfyFile, pvc.getReferenceMap());
        }
    }

    public @NonNull Project getProject() {
        return project;
    }

    public @NonNull PVC getPVC() {
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

    public String getScriptText() {
        return script;
    }

    /**
     * Parses a script as string representation and sets the parsed AST to null.
     *
     * @param script string representation of script
     */
    public void setScriptText(String script) {
        if (this.getScriptText() != null) {
            saveOldDataStructures();
        }

        this.script = script;
        this.scriptAST = null;

        this.proofStatus.setValue(ProofStatus.CHANGED_SCRIPT);
    }

    /**
     * Interpret Script. A script must have been set previously.
     *
     * This will also parse the previously set script text. After this
     * getProofScript()} will return a valid script, if parsing is successful.
     */
    public void interpretScript() {
        assert script != null;

        Interpreter interpreter = new Interpreter(this);
        try {
            // TODO Exception handling
            this.scriptAST = Scripts.parseScript(script);

            interpreter.interpret(scriptAST);
            ProofNode newRoot = interpreter.getRootNode();
            this.proofRoot = newRoot;

            publishReferences();

            this.failException = null;
            proofStatus.setValue(newRoot.allLeavesClosed() ?
                    ProofStatus.CLOSED : ProofStatus.OPEN);
        } catch(Exception ex) {
            // publish the proof root even if the proof has (partially) failed.
            this.proofRoot = interpreter.getRootNode();
            this.failException = ex;

            // TODO proof state handling.
            proofStatus.setValue(ProofStatus.FAILING);
        }
    }

    private void publishReferences() {
        Deque<ProofNode> todo = new LinkedList<>();
        todo.add(proofRoot);
        while (!todo.isEmpty()) {
            ProofNode node = todo.removeFirst();
            if (node.getChildren() != null) {
                try {
                    graph.addFromRuleApplication(this, node, node.getChildren());
                } catch (RuleException e) {
                    System.err.println("Reference graph is incomplete due to exception:");
                    e.printStackTrace();
                }

                if (node.getChildren().size() > 0) {
                    ProofNode child = node.getChildren().get(0);
                    if(child.getCommand() != null) {
                        try {
                            graph.addFromScriptNode(child.getCommand(), node, this);
                        } catch (RuleException e) {
                            System.err.println("Reference graph is incomplete due to exception:");
                            e.printStackTrace();
                        }
                    }
                }

                todo.addAll(node.getChildren());
            }
        }

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
    public Script getProofScript() {
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