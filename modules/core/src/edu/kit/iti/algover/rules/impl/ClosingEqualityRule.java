package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.RuleUtil;

import java.util.HashMap;
import java.util.Optional;

/**
 * Created by jklamroth on 1/11/18.
 */
public class ClosingEqualityRule extends AbstractProofRule {

    public ClosingEqualityRule() {
        super(createParams(), new HashMap<>());
    }

    static private HashMap<String, Class<?>> createParams() {
        HashMap<String, Class<?>> params = new HashMap<>();
        params.put("on", Term.class);
        return params;
    }

    @Override
    public String getName() {
        return "closingEqualityRule";
    }

    @Override
    public ProofRuleApplication considerApplication(ProofNode target, Sequent selection, TermSelector selector) throws RuleException {
        if(selector == null) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }
        ProofFormula f = selector.selectTopterm(target.getSequent());
        Term t = f.getTerm();
        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);
        TermSelector.SequentPolarity pol;
        if(selector.isAntecedent()) {
            pol = TermSelector.SequentPolarity.SUCCEDENT;
        } else {
            pol = TermSelector.SequentPolarity.ANTECEDENT;
        }
        if(!RuleUtil.matchSubtermInPolarity(pol, t::equals, target.getSequent().getSuccedent()).equals(Optional.empty())) {
            builder.setTranscript("closingEqualityRule on='" + t + "';");
            builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);
        } else {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        return builder.build();
    }

    @Override
    public ProofRuleApplication makeApplication(ProofNode target, Parameters parameters) throws RuleException {
        target.setIsclosed(true);
        return new ProofRuleApplicationBuilder(this).build();
    }
}
