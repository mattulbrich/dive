/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.RuleUtil;

import java.util.Collections;
import java.util.List;

public class RemoveAssumptionRule extends AbstractProofRule {

    public RemoveAssumptionRule() {
        super(ON_PARAM);
    }

    @Override
    public String getName() {
        return "removeAssumption";
    }

    @Override
    public ProofRuleApplication considerApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        Term on = parameters.getValue(ON_PARAM);
        List<TermSelector> l = RuleUtil.matchSubtermsInSequent(on::equals, target.getSequent());
        if (l.size() != 1) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }
        TermSelector selector = l.get(0);
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
        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);

        Term toDelete = parameters.getValue(ON_PARAM);

        builder.newBranch()
                .addDeletionsAntecedent(Collections.singletonList(new ProofFormula(toDelete)));

        return builder.build();
    }
}
