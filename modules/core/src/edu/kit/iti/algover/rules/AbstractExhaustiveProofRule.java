package edu.kit.iti.algover.rules;

import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.term.Sequent;

/**
 * Created by jonasklamroth on 31.03.18.
 */
public abstract class AbstractExhaustiveProofRule extends AbstractProofRule {
    @Override
    public abstract String getName();

    @Override
    public abstract ProofRuleApplication considerApplication(ProofNode target, Sequent selection, TermSelector selector) throws RuleException;

    @Override
    public abstract ProofRuleApplication makeApplication(ProofNode target, Parameters parameters) throws RuleException;

    public ProofRuleApplication makeExhaustiveApplication(ProofNode target, Parameters parameters) throws RuleException {
        return null;
    }
}
