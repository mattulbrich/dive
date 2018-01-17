package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.term.Sequent;

/**
 * Created by jklamroth on 1/17/18.
 */
public class MockUpClosing extends AbstractProofRule {

    @Override
    public String getName() {
        return "mockUpClosing";
    }

    @Override
    public ProofRuleApplication considerApplication(ProofNode target, Sequent selection, TermSelector selector) throws RuleException {
        return null;
    }

    @Override
    public ProofRuleApplication makeApplication(ProofNode target, Parameters parameters) throws RuleException {
        return null;
    }
}
