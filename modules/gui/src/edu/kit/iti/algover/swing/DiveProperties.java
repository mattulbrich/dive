/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.swing;

import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.swing.script.ProofNodeCheckpoint;
import edu.kit.iti.algover.swing.util.Property;
import edu.kit.iti.algover.swing.util.Signal;

public class DiveProperties {

    /**
     * Property key indicating that an automatic proof is on the run. This will
     * be set by all actions in actions.auto. <br>
     * Type: Boolean
     */
    public final Property<Boolean> onGoingProof =
            new Property<>("onGoingProof", Boolean.class, true);

    /**
     * There are 3 viewports and they can be switched
     */
    public final Property<Viewport> viewPort =
            new Property<>("viewPort", Viewport.class, null);

    /**
     * The currently loaded project.
     * Initially null, but never set to null afterwards.
     */
    public final Property<Project> project =
            new Property<>("project", Project.class, null);

    /**
     * The currently active PVC.
     * Null in the beginning after loading a project.
     * This is set to null if the code in a program text editor has changed.
     */
    public final Property<PVC> activePVC =
            new Property<>("pvc", PVC.class, null);

    /**
     * This is set to true if the code in a program text editor has changed.
     * Set to true/false by first reload.
     */
    public final Property<Boolean> noProjectMode =
            new Property<>("noProjectMode", Boolean.class, null);

    /**
     * This is set to true if the code in a program text editor has changed.
     * It is reset to false once the source files have been saved.
     */
    public final Property<Boolean> unsavedChanges =
            new Property<>("unsavedChanges", Boolean.class, false);

    /**
     * A signal to indicate that this dive center has been shut down.
     * Goes from false to true at most once.
     */
    public final Property<Boolean> terminated =
            new Property<>("terminated", Boolean.class, false);

    /**
     * Write some text at the current position into the script window.
     */
    public final Signal<String> insertIntoScriptCaret =
            Signal.newSignal("insertIntoScriptCaret", String.class);

    /**
     * Write some text at the command position into the script window.
     */
    public final Signal<String> insertIntoScriptCommand =
            Signal.newSignal("insertIntoScriptCommand", String.class);

    /**
     * The current selection proof node within a pvc.
     *
     * This contains information on the position within the script and allows
     * actions and components to display special purpose information.
     *
     * May be null if no PVC or no valid proof node available.
     */
    public Property<ProofNodeCheckpoint> proofNodeCheckpoint =
            new Property<>("proofNode", ProofNodeCheckpoint.class, null);

    /**
     * The currently selected term (via selector) within a the current
     * proofnode.
     * Reset to null if proofnode is changed.
     */
    public Property<TermSelector> termSelector =
            new Property<>("termSelector", TermSelector.class, null);

    /**
     * Property key to indicate that a proof node has been selected.
     * Type: ProofNode
     */
    public static final String SELECTED_PROOFNODE = "pseudo.selectedProofNode";

    /**
     * Property key to indicate that a rule application has been selected.
     * Type: RuleApplication
     */
    public static final String SELECTED_RULEAPPLICATION = "pseudo.selectedRuleApplication";

    /**
     * Property key to denote the verbosity of the display Type: int
     */
    public static final String TREE_VERBOSITY = "pseudo.tree.verbosity";

    /**
     * Property key to denote whether numbers should be printed in display Type:
     * boolean
     */
    public static final String TREE_SHOW_NUMBERS = "pseudo.tree.shownumbers";

    /**
     * Property key to denote whether program traces should be highlighted or
     * not<br>
     * Type: boolean
     */
    public static final String CODE_PANE_SHOW_TRACE = "pseudo.program.showtrace";

    /**
     * Notification signal to indicate that a node in the proof has been
     * changed. Activated every time that the proof is changed (observing the
     * proof)<br>
     *
     * Type: {@literal List<ProofNode>}
     */
    public static final String PROOFNODES_HAVE_CHANGED = "pseudo.proofnode_changed";

    /**
     * Notification signal to indicate that the proof has changed. This is
     * called after an action on the proof has finished. This notification may
     * come after 0, 1 or several proof node changes to the proof.
     */
    public static final String PROOFTREE_HAS_CHANGED = "pseudo.prooftree_changed";

    /**
     * Notification signal to indicate that an ongoing action is to be stopped.
     * Typically thrown when pressing the proof button in "stop" mode.
     */
    public static final String STOP_REQUEST = "pseudo.stop_request";

    /**
     * Notification signal to indicate that this proof center has reached the end
     * of its live cycle. Resources should be freed.
     */
    public static final String TERMINATION = "pseudo.termination";
}
