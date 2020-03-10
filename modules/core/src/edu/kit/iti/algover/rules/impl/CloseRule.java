/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.RuleUtil;
import edu.kit.iti.algover.util.Util;

import java.util.Set;
import java.util.stream.Collectors;

public class CloseRule extends DefaultFocusProofRule {

    @Override
    public String getName() {
        return "close";
    }

    @Override
    public String getCategory() {
        return ProofRuleCategories.PROPOSITIONAL;
    }

    @Override
    protected TermParameter getDefaultOnParameter(ProofNode target) throws NotApplicableException {

        Set<Term> terms = target.getSequent().getAntecedent().stream().map(p -> p.getTerm()).collect(Collectors.toSet());
        terms.retainAll(Util.map(target.getSequent().getSuccedent(), p -> p.getTerm()));

        if (terms.isEmpty()) {
            // Did not find a term present on both sides
            throw new NotApplicableException("No term is present in both antecedent and succedent");
        }

        return new TermParameter(terms.iterator().next(), target.getSequent());
    }

    @Override
    public ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {

        TermParameter onParam = parameters.getValue(ON_PARAM_OPT);
        Term on = onParam.getTerm();
        boolean presentInAntecedent = RuleUtil.matchTopLevelInAntedecent(on::equals, target.getSequent()).isPresent();
        boolean presentInSuccedent = RuleUtil.matchTopLevelInSuccedent(on::equals, target.getSequent()).isPresent();

        if (!presentInAntecedent || !presentInSuccedent) {
            throw new NotApplicableException("'on' parameter of close rule is not present on both sides of" +
                    " the sequent");
        }


        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);

        builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);

        builder.setClosing();

        return builder.build(); // no branches -> closing the proof

    }
}
