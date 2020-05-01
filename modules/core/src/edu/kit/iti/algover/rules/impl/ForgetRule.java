/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */
package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.FocusProofRule;
import edu.kit.iti.algover.rules.NoFocusProofRule;
import edu.kit.iti.algover.rules.NotApplicableException;
import edu.kit.iti.algover.rules.ParameterDescription;
import edu.kit.iti.algover.rules.ParameterType;
import edu.kit.iti.algover.rules.Parameters;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.ProofRuleApplication.Applicability;
import edu.kit.iti.algover.rules.ProofRuleApplicationBuilder;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermParameter;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;

/**
 * For debbugging purposes mainly.
 *
 * Forget a formula on the sequent.
 *
 * @author mattias
 */
public class ForgetRule extends FocusProofRule {

    public ForgetRule() {
        super();
    }

    @Override
    public String getCategory() {
        return ProofRuleCategories.DEBUG;
    }

    @Override
    public String getName() {
        return "forget";
    }

    @Override
    protected ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {

        TermParameter termParameter = parameters.getValue(ON_PARAM_REQ);
        if (termParameter == null) {
            ProofRuleApplicationBuilder pra = new ProofRuleApplicationBuilder(this);
            return pra.setApplicability(Applicability.APPLICABLE)
                .setParameters(parameters)
                .setApplicability(Applicability.INSTANTIATION_REQUIRED)
                .build();
        }

        TermSelector selector = termParameter.getTermSelector();
        if(!selector.isToplevel()) {
            throw new NotApplicableException();
        }

        ProofFormula formula = selector.selectTopterm(target.getSequent());

        ProofRuleApplicationBuilder pra = new ProofRuleApplicationBuilder(this);
        pra.setApplicability(Applicability.APPLICABLE);
        if (selector.isAntecedent()) {
            pra.newBranch().addDeletionsAntecedent(formula);
        } else {
            pra.newBranch().addDeletionsSuccedent(formula);
        }

        return pra.build();
    }
}
