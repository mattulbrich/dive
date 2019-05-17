package edu.kit.iti.algover.referenceHighlighting;

import edu.kit.iti.algover.references.CodeReferenceTarget;
import edu.kit.iti.algover.references.ProofTermReferenceTarget;
import edu.kit.iti.algover.references.UserInputReferenceTarget;

import java.util.Set;

/**
 * Encapsulation of all computed ReferenceTarget to highlight
 */
public class ReferenceHighlightingObject {



    private ProofTermReferenceTarget selectedTarget;

    private Set<CodeReferenceTarget> codeReferenceTargetSet;

    private Set<ProofTermReferenceTarget> proofTermReferenceTargetSet;

    private Set<UserInputReferenceTarget> userInputReferenceTargetSet;

    //private Set<DescriptionReferenceTarget> descriptionReferenceTargetSet;


    public Set<UserInputReferenceTarget> getUserInputReferenceTargetSet() {
        return userInputReferenceTargetSet;
    }

    public void setUserInputReferenceTargetSet(Set<UserInputReferenceTarget> userInputReferenceTargetSet) {
        this.userInputReferenceTargetSet = userInputReferenceTargetSet;
    }

    public Set<CodeReferenceTarget> getCodeReferenceTargetSet() {
        return codeReferenceTargetSet;
    }

    public void setCodeReferenceTargetSet(Set<CodeReferenceTarget> codeReferenceTargetSet) {
        this.codeReferenceTargetSet = codeReferenceTargetSet;
    }

    public Set<ProofTermReferenceTarget> getProofTermReferenceTargetSet() {
        return proofTermReferenceTargetSet;
    }

    public void setProofTermReferenceTargetSet(Set<ProofTermReferenceTarget> proofTermReferenceTargetSet) {
        this.proofTermReferenceTargetSet = proofTermReferenceTargetSet;
    }


    public ProofTermReferenceTarget getSelectedTarget() {
        return this.selectedTarget;
    }

    public void setSelectedTarget(ProofTermReferenceTarget selectedTarget) {
        this.selectedTarget = selectedTarget;
    }
}
