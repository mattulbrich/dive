package edu.kit.iti.algover.refrenceTypes;

import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.SubtermSelector;
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
    private final ProofNodeSelector proofNodeAfter;

    public TermReferencesBuilder(ProofNodeSelector proofNodeBefore, ProofNodeSelector proofNodeAfter) {
        this.proofNodeBefore = proofNodeBefore;
        this.proofNodeAfter = proofNodeAfter;
    }

    private ReferenceSet buildReferencesAfterApplication(
        Sequent before, Sequent after, TermSelector beforeChanged, TermSelector afterChanged) {
        ReferenceSet references = new ReferenceSet();
        try {
            Term termBefore = beforeChanged.selectSubterm(before);
            Term termAfter = afterChanged.selectSubterm(after);

            TermCollector collectTermsBefore = new TermCollector();
            TermCollector collectTermsAfter = new TermCollector();

            termBefore.accept(collectTermsBefore, new SubtermSelector());
            termAfter.accept(collectTermsAfter, new SubtermSelector());

            Map<SubtermSelector, Term> collectedBefore = collectTermsBefore.getCollectedTerms();
            Map<SubtermSelector, Term> collectedAfter = collectTermsAfter.getCollectedTerms();

            for (Map.Entry<SubtermSelector, Term> entry : collectedAfter.entrySet()) {
                SubtermSelector subselectorAfter = entry.getKey();
                Term term = entry.getValue();

                for (Map.Entry<SubtermSelector, Term> beforeEntry : collectedBefore.entrySet()) {
                    SubtermSelector subselectorBefore = beforeEntry.getKey();
                    // reference equality means a term from before was referenced
                    if (beforeEntry.getValue() == term) {
                        references.addReference(
                            new ProofTermReferenceTarget(proofNodeBefore, new TermSelector(beforeChanged, subselectorBefore)),
                            new ProofTermReferenceTarget(proofNodeAfter, new TermSelector(afterChanged, subselectorAfter))
                        );
                    }
                }
            }
        } catch (RuleException e) {
            e.printStackTrace(); //TODO: Handle errors
        }
        return references;
    }

}
