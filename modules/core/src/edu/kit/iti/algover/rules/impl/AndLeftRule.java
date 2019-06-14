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
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.match.Matching;
import edu.kit.iti.algover.term.match.SequentMatcher;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.RuleUtil;

import java.util.List;

/**
 * Created by jklamroth on 5/22/18.
 */
public class AndLeftRule extends AbstractProofRule {
    public AndLeftRule() {
        super(ON_PARAM);
    }

    @Override
    public boolean mayBeExhaustive() {
        return true;
    }

    @Override
    public String getName() {
        return "andLeft";
    }

    @Override
    public String getCategory() {
        return ProofRuleCategories.PROPOSITIONAL;
    }

    @Override
    protected ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {

        TermSelector selector = parameters.getValue(ON_PARAM).getTermSelector();

        if(!selector.isToplevel()) {
            throw NotApplicableException.onlyToplevel(this);
        }
        if(!selector.isAntecedent()) {
            throw NotApplicableException.onlyAntecedent(this);
        }

        ProofFormula formula = selector.selectTopterm(target.getSequent());
        Term term = formula.getTerm();
        if (!(term instanceof ApplTerm)) {
            throw NotApplicableException.onlyOperator(this, "&&");
        }
        ApplTerm appl = (ApplTerm) term;
        FunctionSymbol fs = appl.getFunctionSymbol();

        if (fs != BuiltinSymbols.AND) {
            throw NotApplicableException.onlyOperator(this, "&&");
        }

        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);

        builder.newBranch().addReplacement(selector, appl.getTerm(0)).
                addAdditionAntecedent(new ProofFormula(appl.getTerm(1)));

        builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);

        return builder.build();
    }
}
