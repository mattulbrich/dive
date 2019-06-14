/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */
package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.AbstractProofRule;
import edu.kit.iti.algover.rules.NotApplicableException;
import edu.kit.iti.algover.rules.ParameterDescription;
import edu.kit.iti.algover.rules.ParameterType;
import edu.kit.iti.algover.rules.Parameters;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.ProofRuleApplicationBuilder;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermParameter;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;

/**
 * For debbugging purposes mainly.
 * Unsound assumption rule that adds to the antecendent
 * @author mattias
 */
public class AssumeRule extends AbstractProofRule {
    private static final ParameterDescription<TermParameter> WITH_PARAM =
            new ParameterDescription<>("#1", ParameterType.TERM, true);

    public AssumeRule() {
        super(WITH_PARAM);
    }

    @Override
    public String getCategory() {
        return ProofRuleCategories.DEBUG;
    }

    @Override
    public String getName() {
        return "assume";
    }

    @Override
    protected ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {

        Term with = parameters.getValue(WITH_PARAM).getTerm();

        if (!with.getSort().equals(Sort.BOOL)) {
            throw NotApplicableException.requiredSort(this, WITH_PARAM, Sort.BOOL, with.getSort());
        }

        ProofRuleApplicationBuilder pra = new ProofRuleApplicationBuilder(this);
        pra.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);
        pra.newBranch().addAdditionAntecedent(new ProofFormula(with)).setLabel("addedHypothesis");

        return pra.build();
    }
}
