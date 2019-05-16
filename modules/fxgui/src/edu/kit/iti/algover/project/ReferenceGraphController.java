package edu.kit.iti.algover.project;

import edu.kit.iti.algover.editor.EditorController;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.references.CodeReferenceTarget;
import edu.kit.iti.algover.references.ProofTermReferenceTarget;
import edu.kit.iti.algover.references.ReferenceGraph;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.sequent.SequentTabViewController;

import java.util.HashSet;
import java.util.Set;
import java.util.logging.Logger;

public class ReferenceGraphController {

    private EditorController editorController;
    private SequentTabViewController sequentController;

    /**
     * Controller that encapsulates ReferenceHighlighting
     * @param editorCtrl
     * @param sequentController
     */
    public ReferenceGraphController(EditorController editorCtrl, SequentTabViewController sequentController){
        this.editorController = editorCtrl;
        this.sequentController = sequentController;
    }

    /**
     * Highlight all referenceTarget for a given ProofTermReferenceTarget that was selected by a user using shift+click
     * in the sequentview
     * @param selectedTarget
     */
    public void highlight(ProofTermReferenceTarget selectedTarget){
        Proof activeProof = sequentController.getActiveSequentController().getActiveProof();

        if (selectedTarget != null) {
            System.out.println("Selected termReference = " + selectedTarget);
            ReferenceGraph referenceGraph = activeProof.getGraph();
            //compute predecessors
            //Set<ReferenceTarget> predecessors = referenceGraph.allPredecessors(termRef);
            //Set<CodeReferenceTarget> codeReferenceTargets = filterCodeReferences(predecessors);
            Set<ProofTermReferenceTarget> proofTermReferenceTargets = referenceGraph.computeHistory(selectedTarget, activeProof);

            Set<CodeReferenceTarget> codeReferenceTargets = referenceGraph.allPredecessorsWithType(selectedTarget, CodeReferenceTarget.class);

            editorController.viewReferences(codeReferenceTargets);
            sequentController.viewReferences(proofTermReferenceTargets, selectedTarget);

        } else {
            editorController.viewReferences(new HashSet<>());
        }
        try {
            Logger.getGlobal().info("Searched for references for selection "+selectedTarget.getTermSelector().selectSubterm(selectedTarget.getProofNodeSelector().get(activeProof).getSequent()));
        } catch (RuleException e) {

            Logger.getGlobal().warning("There was a problem computing the references.");
        }
    }



}
/*
*  /*
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
