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
import edu.kit.iti.algover.util.ExcusableValue;

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
    protected ExcusableValue<ProofRuleApplication, RuleException> makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        TermSelector selector = parameters.getValue(ON_PARAM).getTermSelector();

        if(!selector.isToplevel()) {
            return regret("orRight may only be applied to TopLevel terms.");
        }
        if(!selector.isSuccedent()) {
            return regret("orRight may only be applied on the succedent.");
        }

        ProofFormula formula = selector.selectTopterm(target.getSequent());
        Term term = formula.getTerm();
        if (!(term instanceof ApplTerm)) {
            return regret("orRight may only be applied to or terms.");
        }
        ApplTerm appl = (ApplTerm) term;
        FunctionSymbol fs = appl.getFunctionSymbol();

        if (fs != BuiltinSymbols.OR) {
            return regret("orRight may only be applied to or terms.");
        }

        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);

        builder.newBranch().addReplacement(selector, appl.getTerm(0)).
                addAdditionsSuccedent(new ProofFormula(appl.getTerm(1)));
        builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);

        return ExcusableValue.value(builder.build());
    }
}
