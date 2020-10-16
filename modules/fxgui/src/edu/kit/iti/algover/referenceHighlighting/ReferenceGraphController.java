package edu.kit.iti.algover.referenceHighlighting;

import edu.kit.iti.algover.Lookup;
import edu.kit.iti.algover.PropertyManager;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.references.CodeReferenceTarget;
import edu.kit.iti.algover.references.ProofTermReferenceTarget;
import edu.kit.iti.algover.references.ReferenceGraph;
import edu.kit.iti.algover.references.ScriptReferenceTarget;
import edu.kit.iti.algover.rules.RuleException;
import org.controlsfx.dialog.ExceptionDialog;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.logging.Logger;
import java.util.stream.Collectors;

/**
 * Controls computing the referenceTargets and creating the
 * ReferenceObjects for the classes implementing
 * the HighlightingReferencesHandler
 */
public class ReferenceGraphController {


    private final Lookup lookup;


    public ReferenceGraphController(Lookup lookup) {
        this.lookup = lookup;
        PropertyManager.getInstance().selectedTermForReference.addListener(((observable, oldValue, newValue) -> {
            this.highlightAllReferenceTargets(new ProofTermReferenceTarget(
                    PropertyManager.getInstance().currentProofNodeSelector.get(), newValue));
        }));
    }

    /**
     * Highlight all referenceTarget for a given ProofTermReferenceTarget that was selected by a user using shift+click
     * in the sequentview
     * @param selectedTarget
     */
    public void highlightAllReferenceTargets(ProofTermReferenceTarget selectedTarget){
        if(selectedTarget != null && selectedTarget.getTermSelector() == null) {
            removeReferenceHighlighting();
            return;
        }

        Proof activeProof = PropertyManager.getInstance().currentProof.get();

        if (selectedTarget != null) {

            Set<ProofTermReferenceTarget> proofTermReferenceTargets = computeProofTermRefTargets(selectedTarget, activeProof);
            Set<CodeReferenceTarget> codeReferenceTargets = computeCodeRefTargets(selectedTarget, activeProof);
            codeReferenceTargets = codeReferenceTargets.stream().
                    filter(codeReferenceTarget -> codeReferenceTarget.getEndToken().getCharPositionInLine() >= 0).
                    collect(Collectors.toSet());
            Set<ScriptReferenceTarget> scriptReferenceTargetSet = computeScriptRefTargets(selectedTarget, activeProof);

            //build the ReferenceObject
            ReferenceHighlightingObject referenceObj = new ReferenceHighlightingObject();
            referenceObj.setCodeReferenceTargetSet(codeReferenceTargets);
            referenceObj.setProofTermReferenceTargetSet(proofTermReferenceTargets);
            referenceObj.setSelectedTarget(selectedTarget);
            referenceObj.setScriptReferenceTargetSet(scriptReferenceTargetSet);

            //call all handlers
            for (ReferenceHighlightingHandler referenceHighlightingHandler : lookup.lookupAll(ReferenceHighlightingHandler.class)) {
                referenceHighlightingHandler.handleReferenceHighlighting(referenceObj);
            }

            if(codeReferenceTargets.size() > 0) {
                PropertyManager.getInstance().currentlyDisplayedView.set(1);
            } else if(scriptReferenceTargetSet.size() > 0) {
                PropertyManager.getInstance().currentlyDisplayedView.set(2);
            }
            // editorController.viewReferences(codeReferenceTargets);
            // sequentController.viewReferences(proofTermReferenceTargets, selectedTarget);
            //Collection<RuleApplicationController> ruleApplicationControllers = lookup.lookupAll(RuleApplicationController.class);
            //RuleApplicationController ruleApplicationController = ruleApplicationControllers.iterator().next();
            //ScriptController scriptController = ruleApplicationController.getScriptController();
            //scriptController.viewReferences(proofTermReferenceTargets);
            //scriptController.viewReferences(scriptReferenceTargetSet);

       } else {
           Logger.getGlobal().warning("Could not compute references.");
        }
        try {
            Logger.getGlobal().info("Searched for references for selection "
                    + selectedTarget.getTermSelector()
                    .selectSubterm(
                            selectedTarget.getProofNodeSelector().get(activeProof).getSequent()));
        } catch (RuleException e) {
            ExceptionDialog ed = new ExceptionDialog(e);
            ed.showAndWait();
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
        Set<ProofTermReferenceTarget> history = proof.getReferenceGraph().computeHistory(selectedTarget, proof);
        return history;
    }


    private Set<CodeReferenceTarget> computeCodeRefTargets(ProofTermReferenceTarget selectedTarget, Proof proof){
        Set<CodeReferenceTarget> targetsToHighlight = new HashSet<>();
        ReferenceGraph referenceGraph = proof.getReferenceGraph();
        if(referenceGraph != null) {
            targetsToHighlight = referenceGraph.allPredecessorsWithType(selectedTarget, CodeReferenceTarget.class);
            //we haven't found a direct reference yet and we are not in the root node
            if(targetsToHighlight.isEmpty() && selectedTarget.getProofNodeSelector().getParentSelector() != null){
               List<ProofTermReferenceTarget> descedents = referenceGraph.computeHistorySorted(selectedTarget, proof);
                ProofTermReferenceTarget root = descedents.get(0);
                targetsToHighlight = referenceGraph.allPredecessorsWithType(root, CodeReferenceTarget.class);

            }
        }
        return targetsToHighlight;



    }

    private Set<ScriptReferenceTarget> computeScriptRefTargets(ProofTermReferenceTarget selectedTarget, Proof proof){
        Set<ScriptReferenceTarget> targetsToHighlight = new HashSet<>();
        ReferenceGraph referenceGraph = proof.getReferenceGraph();
        if(referenceGraph != null) {
            //TODO
            //First: find nodes that contain selectedTarget and a scriptReferenceTarget
            targetsToHighlight = referenceGraph.allSuccessorsWithType(selectedTarget, ScriptReferenceTarget.class);
            //Second: if not contained, find the direct parent of the selected target and ask for script ReferenceTargets
            if(targetsToHighlight.isEmpty()){
                ProofTermReferenceTarget proofTermReferenceTarget = null;
                try {
                    proofTermReferenceTarget = referenceGraph.computeTargetBeforeChange(proof, selectedTarget);
                    //  Set<ProofTermReferenceTarget> directParents = referenceGraph.findDirectParents(selectedTarget, proof);
                    //Third, repeat until root is reached or parents are found
                    targetsToHighlight = referenceGraph.allSuccessorsWithType(proofTermReferenceTarget, ScriptReferenceTarget.class);

                } catch (RuleException e) {
                    e.getMessage().concat("Error while handling ReferenceTargets");
                    ExceptionDialog ed = new ExceptionDialog(e);
                    ed.showAndWait();
                }

            }
        }
        return targetsToHighlight;



    }

    public void removeReferenceHighlighting() {
        for (ReferenceHighlightingHandler referenceHighlightingHandler : lookup.lookupAll(ReferenceHighlightingHandler.class)) {
            referenceHighlightingHandler.removeReferenceHighlighting();
        }
    }
}
