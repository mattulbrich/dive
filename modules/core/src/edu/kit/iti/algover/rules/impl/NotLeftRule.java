/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuildException;

import java.util.Collections;

/**
 * Created by jklamroth on 1/11/18.
 */
public class NotLeftRule extends AbstractProofRule {

    public NotLeftRule() {
        super(ON_PARAM);
    }

    @Override
    public String getName() {
        return "notLeft";
    }

    @Override
    public ProofRuleApplication considerApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);

        TermSelector selector = parameters.getValue(ON_PARAM).getTermSelector();

        if(selector == null || selector.isToplevel()) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        ProofFormula formula = selector.selectTopterm(target.getSequent());
        Term term = formula.getTerm();
        if(!(term instanceof ApplTerm)) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);

        try {
            builder.newBranch().addDeletionsAntecedent(Collections.singletonList(new ProofFormula(term)))
                    .addAdditionsSuccedent(new ProofFormula(new ApplTerm(BuiltinSymbols.NOT, term)));
        } catch(TermBuildException e){
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        return builder.build();
    }

    @Override
    public ProofRuleApplication makeApplicationImpl_OLD(ProofNode target, Parameters parameters) throws RuleException {
        Term on = parameters.getValue(ON_PARAM).getTerm();

        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);
        try {
            builder.newBranch().addDeletionsAntecedent(Collections.singletonList(new ProofFormula(on)))
                    .addAdditionsSuccedent(new ProofFormula(new ApplTerm(BuiltinSymbols.NOT, on)));
        } catch (TermBuildException e) {
            throw new RuleException();
        }

        return builder.build();
    }
}
