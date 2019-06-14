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
import edu.kit.iti.algover.rules.ProofRuleApplication.Applicability;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.util.RuleUtil;

/**
 * Created by jklamroth on 5/16/18.
 */
public class AddHypothesisRule extends AbstractProofRule {
    public static final ParameterDescription<TermParameter> WITH_PARAM =
            new ParameterDescription<>("with", ParameterType.TERM, true);

    public AddHypothesisRule() {
        super(WITH_PARAM);
    }

    @Override
    public String getName() {
        return "addHypothesis";
    }

    @Override
    protected ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        return apply(target, parameters);
    }

    private ProofRuleApplication apply(ProofNode target, Parameters parameters) throws RuleException {
        TermParameter withParam = parameters.getValue(WITH_PARAM);

        if (withParam == null) {
            ProofRuleApplicationBuilder pra = new ProofRuleApplicationBuilder(this);
            pra.setApplicability(Applicability.INSTANTIATION_REQUIRED);
            return pra.build();
        }

        Term with = withParam.getTerm();

        if(!with.getSort().equals(Sort.BOOL)) {
            throw NotApplicableException.requiredSort(this, WITH_PARAM, Sort.BOOL, with.getSort());
        }

        ProofRuleApplicationBuilder pra = new ProofRuleApplicationBuilder(this);
        pra.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);
        pra.newBranch().addAdditionAntecedent(new ProofFormula(with)).setLabel("addedHypothesis");
        pra.newBranch().addAdditionsSuccedent(new ProofFormula(with)).setLabel("rectification");

        return pra.build();
    }
}
