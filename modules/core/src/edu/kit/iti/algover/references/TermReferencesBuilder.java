/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.references;

import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;

import java.util.Map;

/**
 * Creates Term references between referentially equal parts of
 * two terms (in the sense of java 'pointers'). Can be used to
 * create references between two terms before and after rule
 * application.
 * <p>
 * Using this class, rule application does not have
 * to deal with building references itself. It just needs to preserve
 * the Term instances that are the same between two terms.
 * <p>
 * Created by Philipp on 27.08.2017.
 */
public final class TermReferencesBuilder {

    private final ProofNodeSelector proofNodeBefore;
    private final ReferenceGraph references;
    private final Proof proof;

    public TermReferencesBuilder(ReferenceGraph references, Proof proof, ProofNodeSelector proofNodeBefore)
            throws RuleException {
        this.proofNodeBefore = proofNodeBefore;
        this.references = references;
        this.proof = proof;
        proofNodeBefore.get(proof);
    }

    /**
     * Builds references from {@link ProofTermReferenceTarget}s in the given {@link #proofNodeBefore}
     * to other {@link ProofTermReferenceTarget}s in the given proofNodeAfter whose terms they point to
     * are referentially equal (but at different places obviously).
     * <p>
     * Referentially equal Terms suggest that they were re-used in the new ProofNode after rule
     * application and therefore seem to just have transitioned to there.
     *
     * @param proofNodeAfter the particular node to check for re-occurring terms
     *                       (compared to the given {@link #proofNodeBefore})
     * @param changedTerm    a selector of the term that has been changed
     *                       (the selector that (usually) a rule was applied to)
     * @return itself for method chaining.
     * @throws RuleException in case the ProofNodeSelector or TermSelector were invalid.
     */
    public TermReferencesBuilder buildReferences(
            ProofNodeSelector proofNodeAfter, TermSelector changedTerm)
            throws RuleException {
        proofNodeAfter.get(proof);
        changedTerm.selectSubterm(proofNodeBefore.get(proof).getSequent());
        //build top-level Reference
        ProofTermReferenceTarget from = new ProofTermReferenceTarget(proofNodeBefore, changedTerm);
        ProofTermReferenceTarget to = new ProofTermReferenceTarget(proofNodeAfter, changedTerm);
        references.addReference(from, to);

        buildReferencesAfterApplication(
                proofNodeAfter,
                proofNodeBefore.get(proof).getSequent(),
                proofNodeAfter.get(proof).getSequent(),
                changedTerm);
        return this;
    }

    private void buildReferencesAfterApplication(
            ProofNodeSelector proofNodeAfter, Sequent before, Sequent after, TermSelector changedSelector) throws RuleException {
        try {
            TermCollector collectTermsBefore = new TermCollector();
            TermCollector collectTermsAfter = new TermCollector();

            collectTermsBefore.collectInSequent(before, changedSelector);

            for (int i = 0; i < after.getAntecedent().size(); i++) {
                TermSelector selector = new TermSelector(TermSelector.SequentPolarity.ANTECEDENT, i);
                collectTermsAfter.collectInSequent(after, selector);
            }
            for (int i = 0; i < after.getSuccedent().size(); i++) {
                TermSelector selector = new TermSelector(TermSelector.SequentPolarity.SUCCEDENT, i);
                collectTermsAfter.collectInSequent(after, selector);
            }

            final Map<TermSelector, Term> collectedBefore = collectTermsBefore.getCollectedTerms();
            final Map<TermSelector, Term> collectedAfter = collectTermsAfter.getCollectedTerms();

            collectedBefore.forEach((termSelectorBefore, termBefore) -> {
                // look for referentially equal objects in the sequent after the rule application:
                collectedAfter.forEach((termSelectorAfter, termAfter) -> {
                    if (termAfter == termBefore) { // referential equality
                        ProofTermReferenceTarget from = new ProofTermReferenceTarget(proofNodeBefore, termSelectorBefore);
                        ProofTermReferenceTarget to = new ProofTermReferenceTarget(proofNodeAfter, termSelectorAfter);
                        references.addReference(
                                from,
                                to
                        );
                    }
                });
            });


        } catch (RuleException e) {
            e.printStackTrace();
            // this should _only_ happen, if changedSelector is an invalid selector!
            throw e;
        }
    }

}
