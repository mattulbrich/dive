/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.term.Term;

import java.util.Collections;

public class RemoveAssumptionRule extends FocusProofRule {


    public RemoveAssumptionRule() {
        super(ON_PARAM);
    }

    @Override
    public String getName() {
        return "removeAssumption";
    }

    public ProofRuleApplication considerApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        TermSelector selector = parameters.getValue(ON_PARAM).getTermSelector();
        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);

        if (!selector.isToplevel() || !selector.isAntecedent()) {
            builder.setApplicability(ProofRuleApplication.Applicability.NOT_APPLICABLE);
        } else {
            builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);
            ProofFormula deleted = selector.selectTopterm(target.getSequent());
            builder.newBranch()
                    .addDeletionsAntecedent(Collections.singletonList(deleted));
        }
        return builder.build();
    }

    @Override
    public ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {

        TermParameter onParam = parameters.getValue(ON_PARAM);
        Term on = onParam.getTerm();
        TermSelector selector = parameters.getValue(ON_PARAM).getTermSelector();

        if(!selector.isToplevel()){
            throw NotApplicableException.onlyToplevel(this);
        }
        if(!selector.isAntecedent()){
            throw NotApplicableException.onlyAntecedent(this);
        }

        ProofRuleApplicationBuilder pra = new ProofRuleApplicationBuilder(this);
        pra.newBranch().addDeletionsAntecedent(Collections.singletonList(new ProofFormula(on)));


        pra.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);

        return pra.build();

    }
}
