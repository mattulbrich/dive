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

/**
 * Created by jklamroth on 5/22/18.
 */
public class OrRightRule extends AbstractProofRule {
    public OrRightRule() {
        super(ON_PARAM);
    }

    @Override
    public boolean mayBeExhaustive() {
        return true;
    }

    @Override
    public String getName() {
        return "orRight";
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
        if(!selector.isSuccedent()) {
            throw NotApplicableException.onlySuccedent(this);
        }

        ProofFormula formula = selector.selectTopterm(target.getSequent());
        Term term = formula.getTerm();
        if (!(term instanceof ApplTerm)) {
            throw NotApplicableException.onlyOperator(this, "||");
        }
        ApplTerm appl = (ApplTerm) term;
        FunctionSymbol fs = appl.getFunctionSymbol();

        if (fs != BuiltinSymbols.OR) {
            throw NotApplicableException.onlyOperator(this, "||");
        }

        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);

        builder.newBranch().addReplacement(selector, appl.getTerm(0)).
                addAdditionsSuccedent(new ProofFormula(appl.getTerm(1)));
        builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);

        return builder.build();
    }
}
