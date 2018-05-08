package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.RuleUtil;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

public class CloseRule extends AbstractProofRule {

    public CloseRule() {
        super(
                ON_PARAM
        );
    }

    @Override
    public String getName() {
        return "close";
    }

    @Override
    public ProofRuleApplication considerApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        Term on = parameters.getValue(ON_PARAM);

        try {
            return buildApplication(target, on);
        } catch (RuleException e) {
            ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);
            builder.setApplicability(ProofRuleApplication.Applicability.NOT_APPLICABLE);
            return builder.build();
        }
    }

    @Override
    public ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        Term on = parameters.getValue(ON_PARAM);

        return buildApplication(target, on);
    }

    private ProofRuleApplication buildApplication(ProofNode target, Term on) throws RuleException {
        // make sure that the term specified in 'on' is on both sides of the sequent
        boolean presentInAntecedent = RuleUtil.matchTopLevelInAntedecent(on::equals, target.getSequent()).isPresent();
        boolean presentInSuccedent = RuleUtil.matchTopLevelInSuccedent(on::equals, target.getSequent()).isPresent();

        if (!presentInAntecedent || !presentInSuccedent) {
            throw new RuleException("'on' parameter of closing rule is not present on both sides of" +
                    "the sequent. on=" + on + ", present in antecedent=" + presentInAntecedent +
                    "present in succedent=" + presentInSuccedent);
        }

        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);

        builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);

        builder.setClosing();

        return builder.build(); // no branches -> closing the proof

    }
}
