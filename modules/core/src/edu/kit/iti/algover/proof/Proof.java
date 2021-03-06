/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.nuscript.Interpreter;
import edu.kit.iti.algover.nuscript.ScriptAST;
import edu.kit.iti.algover.nuscript.ScriptAST.Script;
import edu.kit.iti.algover.nuscript.parser.Scripts;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.references.ReferenceGraph;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.util.ObservableValue;
import edu.kit.iti.algover.util.ObservableValue.ChangeListener;
import edu.kit.iti.algover.util.ProofTreeUtil;
import nonnull.NonNull;
import nonnull.Nullable;

import java.util.Collections;
import java.util.Deque;
import java.util.LinkedList;
import java.util.List;

/**
 * Proof Object.
 *
 * This object contains the proof root as well as the script root
 *
 * It is a mutable object. The proof script can be modified and interpretation be triggered.
 *
 * @author Sarah Grebing
 * @author M. Ulbrich, refactoring Jan 2018
 */
public class Proof {

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
     *
     * mutable.
     */
    private @Nullable ProofNode proofRoot;

    /**
     * The script text.
     *
     * mutable, can be null if scriptAST has been set directly.
     */
    private @Nullable String scriptText;

    /**
     * The AST of the script.
     *
     * mutable, can be null if not yet parsed
     * (in the beginning or after setting a script)
     */
    private @Nullable Script scriptAST;

    /**
     * PVC for which this proof object is created
     */
    private final PVC pvc;

    /**
     * The reference graph for the current proof
     */
    private final ReferenceGraph graph;

    /**
     * The exception with which interpretation has failed.
     */
    /*@ invariant failures.isEmpty() <==> poofStatus.getValue() != FAIL; */
    private @NonNull List<Exception> failures = Collections.emptyList();

    /**
     * Create a new proof for a PVC.
     *
     * The project parameter is not necessary.
     *
     * @param project project to which the PVC belongs
     * @param pvc a PVC
     */
    @Deprecated
    public Proof(@NonNull Project project, @NonNull PVC pvc) {
        this(pvc);
        assert project == pvc.getProject();
    }

    /**
     * Create a new proof for a PVC.
     *
     * @param pvc a PVC
     */
    public Proof(@NonNull PVC pvc) {
        this.pvc = pvc;
        this.graph = new ReferenceGraph();
    }

    // --------- Getters

    public @NonNull Project getProject() {
        return pvc.getProject();
    }

    public @NonNull PVC getPVC() {
        return pvc;
    }

    public @Nullable ProofNode getProofRoot() {
        return proofRoot;
    }

    public @NonNull String getPVCName() {
        return pvc.getIdentifier();
    }

    public @NonNull ProofStatus getProofStatus() {
        return proofStatus.getValue();
    }

    public @NonNull List<Exception> getFailures() {
        return failures;
    }

    public @NonNull ReferenceGraph getReferenceGraph() {
        return graph;
    }

    public @Nullable String getScriptText() {
        return scriptText;
    }

    /**
     * Get the proof script or null.
     *
     * Null if the script has not been parsed yet.
     *
     * @return null or the parser result of the script text.
     */
    public @Nullable Script getProofScript() {
        return scriptAST;
    }

    // --------- Modifiers

    public void addProofStatusListener(ObservableValue.ChangeListener<ProofStatus> listener) {
        proofStatus.addObserver(listener);
    }

    public void removeProofStatusListener(ChangeListener<ProofStatus> listener) {
        proofStatus.removeObserver(listener);
    }

    /**
     * Add all code references from a Dafny file to the refrence graph.
     *
     * @param dfyFile the file to use for analysis
     */
    public void addDafnyFileReferences(@NonNull DafnyFile dfyFile) {
        getReferenceGraph().addFromReferenceMap(dfyFile, pvc.getReferenceMap());
    }

    /**
     * Sets a script string representation and sets the parsed AST to null.
     * Set the state to {@link ProofStatus#CHANGED_SCRIPT}.
     *
     * @param script string representation of script
     */
    public void setScriptText(@NonNull String script) {
        this.scriptText = script;
        this.scriptAST = null;
        this.proofStatus.setValue(ProofStatus.CHANGED_SCRIPT);
    }

    /**
     * Sets a script string representation and sets the script text to null.
     * Set the state to {@link ProofStatus#CHANGED_SCRIPT}.
     *
     * @param script string representation of script
     */
    public void setScriptAST (@NonNull Script script) {
        this.scriptAST = script;
        this.scriptText = null;
        this.proofStatus.setValue(ProofStatus.CHANGED_SCRIPT);
    }

    /**
     * Interpret Script. A script must have been set previously.
     *
     * Requires that the proof state is {@link ProofStatus#CHANGED_SCRIPT}.
     *
     * This will also parse the previously set script text (if set via {@link
     * #setScriptText(String)}). No parsing is involved if the script has been
     * set with {@link #setScriptAST(Script)}.
     *
     * Afterwards, {@link #getProofScript()} will return a valid script, if
     * parsing is successful.
     */
    public void interpretScript() {

        assert proofStatus.getValue() == ProofStatus.CHANGED_SCRIPT;

        Interpreter interpreter = new Interpreter(this);

        // Set the new root upfront to keep partial proofs even in case of failure.
        // (Also a syntax error deserves a proof root.)
        this.proofRoot = interpreter.getRootNode();

        if (this.scriptAST == null) {
            assert scriptText != null : "Either ast or text must not be null";
            try {
                this.scriptAST = Scripts.parseScript(scriptText);
            } catch (Exception ex) {
                this.failures = Collections.singletonList(ex);
                this.scriptAST = null;
                proofStatus.setValue(ProofStatus.FAILING);
                return;
            }
        }

        try {
            interpreter.interpret(scriptAST);
            ProofNode newRoot = interpreter.getRootNode();
            this.proofRoot = newRoot;

            publishReferences();

            if(interpreter.hasFailure()) {
                this.failures = interpreter.getFailures();
                this.proofStatus.setValue(ProofStatus.FAILING);
            } else {
                this.failures = Collections.emptyList();
                proofStatus.setValue(newRoot.allLeavesClosed() ?
                        ProofStatus.CLOSED : ProofStatus.OPEN);
            }
            scriptAST.seal();
        } catch(Exception ex) {
            System.err.println("This is an unexpected error (that should never be raised):");
            ex.printStackTrace();
            this.failures = Collections.singletonList(ex);
            proofStatus.setValue(ProofStatus.FAILING);
        }

        // provide consistency
        if (scriptAST != null) {
            scriptText = "";
            for (ScriptAST.Statement stmt: scriptAST.getStatements()){
                scriptText += stmt.toString();
            }
        }

    }


    private void publishReferences() {
        Deque<ProofNode> todo = new LinkedList<>();
        todo.add(proofRoot);
        while (!todo.isEmpty()) {
            ProofNode node = todo.removeFirst();
            List<ProofNode> children = node.getChildren();
            if (children != null) {
                try {
                    graph.addFromRuleApplication(this, node, children);
                } catch (RuleException e) {
                    System.err.println("Reference graph is incomplete due to exception:");
                    e.printStackTrace();
                }

                if (children.size() > 0) {
                    ProofNode child = children.get(0);
                    if(child.getCommand() != null) {
                        try {
                            graph.addFromScriptNode(child.getCommand(), node, this);
                        } catch (RuleException e) {
                            System.err.println("Reference graph is incomplete due to exception:");
                            e.printStackTrace();
                        }
                    }
                }

                todo.addAll(children);
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
}