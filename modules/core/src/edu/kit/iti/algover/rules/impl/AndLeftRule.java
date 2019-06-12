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
    public ProofRuleApplication considerApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        TermSelector selector = parameters.getValue(ON_PARAM).getTermSelector();

        if(!selector.isToplevel()) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }
        if(!selector.isAntecedent()) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        ProofFormula formula = selector.selectTopterm(target.getSequent());
        Term term = formula.getTerm();
        if (!(term instanceof ApplTerm)) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }
        ApplTerm appl = (ApplTerm) term;
        FunctionSymbol fs = appl.getFunctionSymbol();

        if (fs != BuiltinSymbols.AND) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);

        builder.newBranch().addReplacement(selector, appl.getTerm(0)).
                addAdditionAntecedent(new ProofFormula(appl.getTerm(1)));
        builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);

        return builder.build();
    }

    @Override
    protected ProofRuleApplication makeApplicationImpl_OLD(ProofNode target, Parameters parameters) throws RuleException {
        Term on = parameters.getValue(ON_PARAM).getTerm();
        List<TermSelector> l = RuleUtil.matchSubtermsInSequent(on::equals, target.getSequent());
        if(l.size() != 1) {
            throw new RuleException("Matching of on parameter is ambiguous.");
        }
        TermSelector selector = l.get(0);
        if(!selector.isToplevel()) {
            throw new RuleException("andLeft may only be applied to TopLevel terms.");
        }
        if(!selector.isAntecedent()) {
            throw new RuleException("andLeft may only be applied on the antecedent.");
        }

        ProofFormula formula = selector.selectTopterm(target.getSequent());
        Term term = formula.getTerm();
        if (!(term instanceof ApplTerm)) {
            throw new RuleException("andLeft may only be applied to or terms.");
        }
        ApplTerm appl = (ApplTerm) term;
        FunctionSymbol fs = appl.getFunctionSymbol();

        if (fs != BuiltinSymbols.AND) {
            throw new RuleException("andLeft may only be applied to or terms.");
        }

        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);

        builder.newBranch().addReplacement(selector, appl.getTerm(0)).
                addAdditionAntecedent(new ProofFormula(appl.getTerm(1)));
        builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);

        return builder.build();
    }
}
