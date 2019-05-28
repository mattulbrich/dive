package edu.kit.iti.algover.references;


import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.rules.TermSelector;


/**
 * Creates references between ScriptNodes and Terms. A term is part of a reference \<Script, Term\> iff
 * it was either added or replaced by the rule command that is encoded in the
 * ScriptNode
 */
public class ScriptReferenceBuilder {

    private final ScriptReferenceTarget sct;

    private final ProofNodeSelector parentSelector;

    private final Proof proof;

    private final ReferenceGraph graph;

    public ScriptReferenceBuilder(ReferenceGraph referenceGraph, ScriptReferenceTarget sct, ProofNode pNode, Proof proof) {
        this.sct = sct;
        this.parentSelector = new ProofNodeSelector(pNode);
        this.proof = proof;
        this.graph = referenceGraph;

    }




    private void buildReferences(ProofNodeSelector proofNodeAfter, TermSelector changedTerm){
        ProofTermReferenceTarget pt = new ProofTermReferenceTarget(proofNodeAfter, changedTerm);
        graph.addReference(pt, sct);



        //additions and replacements -> dann referenz für jedes Element erzeugen und mit ScriptreferenceTarget verknüpfen
    //    ProofRuleApplication proofRuleApplication = pNode.getProofRuleApplication();
    //    List<ProofNode> children = pNode.getChildren();
    //    ProofNodeSelector parentSel = new ProofNodeSelector(pNode);



    }
}
