package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.RuleUtil;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

public class CloseRule extends AbstractProofRule {

    public CloseRule() {
        super(new ParameterDescription<>("on", ParameterType.TERM, false));
    }

    @Override
    public String getName() {
        return "close";
    }

    @Override
    public ProofRuleApplication considerApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        Term on = null;
        if(parameters.entrySet().size() > 0) {
            on = (Term)parameters.getValue("on");
        }

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
        Term on = null;
        if(parameters.entrySet().size() > 0) {
            on = (Term)parameters.getValue("on");
        }
        return buildApplication(target, on);
    }

    private ProofRuleApplication buildApplication(ProofNode target, Term on) throws RuleException {
        // make sure that the term specified in 'on' is on both sides of the sequent
        if(on != null) {
            boolean presentInAntecedent = RuleUtil.matchTopLevelInAntedecent(on::equals, target.getSequent()).isPresent();
            boolean presentInSuccedent = RuleUtil.matchTopLevelInSuccedent(on::equals, target.getSequent()).isPresent();

            if (!presentInAntecedent || !presentInSuccedent) {
                throw new RuleException("'on' parameter of closing rule is not present on both sides of" +
                        "the sequent. on=" + on + ", present in antecedent=" + presentInAntecedent +
                        "present in succedent=" + presentInSuccedent);
            }
        } else {
            for(Term t1 : target.getSequent().getAntecedent().stream().map(p -> p.getTerm()).collect(Collectors.toList())) {
                for(Term t2 : target.getSequent().getSuccedent().stream().map(p -> p.getTerm()).collect(Collectors.toList())) {
                    if (t1.equals(t2)) {
                        on = t1;
                    }
                }
            }
            if(on == null) {
                throw new RuleException("no on parameter found to apply close rule.");
            }
        }

        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);

        builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);

        builder.setClosing();

        return builder.build(); // no branches -> closing the proof

    }
}
