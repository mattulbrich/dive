package edu.kit.iti.algover.referenceHighlighting;

import edu.kit.iti.algover.Lookup;
import edu.kit.iti.algover.editor.EditorController;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.references.CodeReferenceTarget;
import edu.kit.iti.algover.references.ProofTermReferenceTarget;
import edu.kit.iti.algover.references.ReferenceGraph;
import edu.kit.iti.algover.references.ScriptReferenceTarget;
import edu.kit.iti.algover.rule.RuleApplicationController;
import edu.kit.iti.algover.rule.script.ScriptController;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.sequent.SequentTabViewController;

import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.logging.Logger;
import java.util.stream.Collectors;

public class ReferenceGraphController {


    private final Lookup lookup;


    public ReferenceGraphController(Lookup lookup){
         this.lookup = lookup;
    }

    /**
     * Highlight all referenceTarget for a given ProofTermReferenceTarget that was selected by a user using shift+click
     * in the sequentview
     * @param selectedTarget
     */
    public void highlightAllReferenceTargets(ProofTermReferenceTarget selectedTarget){
        Collection<SequentTabViewController> sequentTabViewControllers = lookup.lookupAll(SequentTabViewController.class);
        if(sequentTabViewControllers.size() < 1){
            //TODO
            throw new RuntimeException("Something went wrong with References");
        }
        SequentTabViewController sequentController = sequentTabViewControllers.iterator().next();

        Proof activeProof = sequentController.getActiveSequentController().getActiveProof();

        if (selectedTarget != null) {
           // System.out.println("Selected termReference = " + selectedTarget);


            Set<ProofTermReferenceTarget> proofTermReferenceTargets = computeProofTermRefTargets(selectedTarget, activeProof);
            Set<CodeReferenceTarget> codeReferenceTargets = computeCodeRefTargets(selectedTarget, activeProof);
            Set<ScriptReferenceTarget> scriptReferenceTargetSet = computeScriptRefTargets(selectedTarget, activeProof);

            ReferenceHighlightingObject referenceObj = new ReferenceHighlightingObject();
            referenceObj.setCodeReferenceTargetSet(codeReferenceTargets);
            referenceObj.setProofTermReferenceTargetSet(proofTermReferenceTargets);
            referenceObj.setSelectedTarget(selectedTarget);

            for (ReferenceHighlightingHandler referenceHighlightingHandler : lookup.lookupAll(ReferenceHighlightingHandler.class)) {
                referenceHighlightingHandler.handleReferenceHighlighting(referenceObj);
            }
           // editorController.viewReferences(codeReferenceTargets);
           // sequentController.viewReferences(proofTermReferenceTargets, selectedTarget);
            //Collection<RuleApplicationController> ruleApplicationControllers = lookup.lookupAll(RuleApplicationController.class);
            //RuleApplicationController ruleApplicationController = ruleApplicationControllers.iterator().next();
            //ScriptController scriptController = ruleApplicationController.getScriptController();
            //scriptController.viewReferences(proofTermReferenceTargets);
            //scriptController.viewReferences(scriptReferenceTargetSet);

        } else {

            //editorController.viewReferences(new HashSet<>());
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

    private Set<ScriptReferenceTarget> computeScriptRefTargets(ProofTermReferenceTarget selectedTarget, Proof proof){
        Set<ScriptReferenceTarget> targetsToHighlight = new HashSet<>();
        ReferenceGraph referenceGraph = proof.getGraph();
        if(referenceGraph != null) {
            //TODO
            //First: find nodes that contain selectedTarget and a scriptReferenceTarget
            targetsToHighlight = referenceGraph.allSuccessorsWithType(selectedTarget, ScriptReferenceTarget.class);
            //Second: if not contained, find the direct parent of the selected target and ask for script ReferenceTargets
            if(targetsToHighlight.isEmpty()){

                Set<ProofTermReferenceTarget> directParents = referenceGraph.findDirectParents(selectedTarget, proof);
                //Third, repeat until root is reached or parents are found


            }
        }
        return targetsToHighlight;



    }

    public void removeReferenceHighlighting() {
        for (ReferenceHighlightingHandler referenceHighlightingHandler : lookup.lookupAll(ReferenceHighlightingHandler.class)) {
            referenceHighlightingHandler.removeReferenceHighlighting();
        }
        //sequentController.removeReferenceHighlighting();
        //editorController.removeReferenceHighlighting();

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
