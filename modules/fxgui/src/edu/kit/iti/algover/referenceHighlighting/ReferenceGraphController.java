package edu.kit.iti.algover.referenceHighlighting;

import edu.kit.iti.algover.editor.EditorController;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.references.CodeReferenceTarget;
import edu.kit.iti.algover.references.ProofTermReferenceTarget;
import edu.kit.iti.algover.references.ReferenceGraph;
import edu.kit.iti.algover.rule.RuleApplicationController;
import edu.kit.iti.algover.rule.script.ScriptController;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.sequent.SequentTabViewController;

import java.util.HashSet;
import java.util.Set;
import java.util.logging.Logger;

public class ReferenceGraphController {

    /**
     * This will be refactored
     */
    private final EditorController editorController;
    private final SequentTabViewController sequentController;
    private final RuleApplicationController ruleApplicationController;

    /**
     * Controller that encapsulates ReferenceHighlighting
     * @param editorCtrl
     * @param sequentController
     */
    public ReferenceGraphController(EditorController editorCtrl, SequentTabViewController sequentController, RuleApplicationController ruleApplicationController){
        this.editorController = editorCtrl;
        this.sequentController = sequentController;
        this.ruleApplicationController = ruleApplicationController;
    }

    /**
     * Highlight all referenceTarget for a given ProofTermReferenceTarget that was selected by a user using shift+click
     * in the sequentview
     * @param selectedTarget
     */
    public void highlightAllReferenceTargets(ProofTermReferenceTarget selectedTarget){

        Proof activeProof = sequentController.getActiveSequentController().getActiveProof();

        if (selectedTarget != null) {
            System.out.println("Selected termReference = " + selectedTarget);


            Set<ProofTermReferenceTarget> proofTermReferenceTargets = computeProofTermRefTargets(selectedTarget, activeProof);
            Set<CodeReferenceTarget> codeReferenceTargets = computeCodeRefTargets(selectedTarget, activeProof);

            editorController.viewReferences(codeReferenceTargets);
            sequentController.viewReferences(proofTermReferenceTargets, selectedTarget);

            ScriptController scriptController = this.ruleApplicationController.getScriptController();
            scriptController.viewReferences(proofTermReferenceTargets);

        } else {
            editorController.viewReferences(new HashSet<>());
        }
        try {
            Logger.getGlobal().info("Searched for references for selection "
                    + selectedTarget.getTermSelector()
                    .selectSubterm(
                            selectedTarget.getProofNodeSelector().get(activeProof).getSequent()));
        } catch (RuleException e) {

            Logger.getGlobal().warning("There was a problem computing the references.");
        }
    }

    /**
     * Compute all ProofTermReferenceTargets to highlight in the scriptView
     * @param selectedTarget
     * @param proof
     * @return
     */
    private Set<ProofTermReferenceTarget> computeProofTermRefTargets(ProofTermReferenceTarget selectedTarget, Proof proof){
        Set<ProofTermReferenceTarget> targetsToHighlight = new HashSet<>();
        Set<ProofTermReferenceTarget> history = proof.getGraph().computeHistory(selectedTarget, proof);

        return history;
    }


    private Set<CodeReferenceTarget> computeCodeRefTargets(ProofTermReferenceTarget selectedTarget, Proof proof){
        Set<CodeReferenceTarget> targetsToHighlight = new HashSet<>();
        ReferenceGraph referenceGraph = proof.getGraph();
        if(referenceGraph != null) {
            targetsToHighlight = referenceGraph.allPredecessorsWithType(selectedTarget, CodeReferenceTarget.class);
        }
        return targetsToHighlight;



    }

}
/*

          //  ReferenceGraph referenceGraph = activeProof.getGraph();
            //compute predecessors
            //Set<ReferenceTarget> predecessors = referenceGraph.allPredecessors(termRef);
            //Set<CodeReferenceTarget> codeReferenceTargets = filterCodeReferences(predecessors);
            //= referenceGraph.computeHistory(selectedTarget, activeProof);

    private static Set<CodeReferenceTarget> filterCodeReferences(Set<ReferenceTarget> predecessors) {
        Set<CodeReferenceTarget> codeReferenceTargets = new HashSet<>();

        predecessors.forEach(reference -> {

            CodeReferenceTarget codeReferenceTarget = reference.accept(new GetReferenceTypeVisitor<>(CodeReferenceTarget.class));
            if (codeReferenceTarget != null) {
                codeReferenceTargets.add(codeReferenceTarget);
            }
        });
        return codeReferenceTargets;
    }

    private static Set<ProofTermReferenceTarget> filterTermReferences(Set<ReferenceTarget> predecessors){
        Set<ProofTermReferenceTarget> codeReferenceTargets = new HashSet<>();
        predecessors.forEach(reference -> {
            ProofTermReferenceTarget codeReferenceTarget = reference.accept(new GetReferenceTypeVisitor<>(ProofTermReferenceTarget.class));
            if (codeReferenceTarget != null) {
                codeReferenceTargets.add(codeReferenceTarget);
            }
        });
        return codeReferenceTargets;
    }*/
