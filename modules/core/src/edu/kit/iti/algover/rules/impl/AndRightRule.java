/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules.impl;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.AbstractProofRule;
import edu.kit.iti.algover.rules.NotApplicableException;
import edu.kit.iti.algover.rules.Parameters;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.ProofRuleApplication.Applicability;
import edu.kit.iti.algover.rules.ProofRuleApplicationBuilder;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.match.Matching;
import edu.kit.iti.algover.term.match.SequentMatcher;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.RuleUtil;

public class AndRightRule extends AbstractProofRule {

    public static final String RULE_NAME = "andRight";

    public AndRightRule() {
        super(ON_PARAM);
    }

    @Override
    public boolean mayBeExhaustive() {
        return true;
    }

    @Override
    public String getName() {
        return RULE_NAME;
    }

    @Override
    public String getCategory() {
        return ProofRuleCategories.PROPOSITIONAL;
    }

    @Override
    public ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        Term on = parameters.getValue(ON_PARAM).getTerm();
        TermSelector selector = parameters.getValue(ON_PARAM).getTermSelector();

        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);

        if (!selector.isToplevel()) {
            throw NotApplicableException.onlyToplevel(this);
        }

        if (!selector.isSuccedent()) {
            throw NotApplicableException.onlySuccedent(this);
        }

        if(!(on instanceof ApplTerm)) {
            throw NotApplicableException.onlyOperator(this, "&&");
        }

        if(((ApplTerm)on).getFunctionSymbol() != BuiltinSymbols.AND) {
            throw NotApplicableException.onlyOperator(this, "&&");
        }

        int no = selector.getTermNo();

        builder.newBranch()
                .addDeletionsSuccedent(target.getSequent().getSuccedent().get(no))
                .addAdditionsSuccedent(new ProofFormula(on.getTerm(0)))
                .setLabel("case 1");

        builder.newBranch()
                .addDeletionsSuccedent(target.getSequent().getSuccedent().get(no))
                .addAdditionsSuccedent(new ProofFormula(on.getTerm(1)))
                .setLabel("case 2");

        builder.setApplicability(Applicability.APPLICABLE);

        return builder.build();
    }
}
