/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.DefaultFocusProofRule;
import edu.kit.iti.algover.rules.NotApplicableException;
import edu.kit.iti.algover.rules.Parameters;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.ProofRuleApplication.Applicability;
import edu.kit.iti.algover.rules.ProofRuleApplicationBuilder;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermParameter;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.RuleUtil;

public class AndRightRule extends DefaultFocusProofRule {

    public static final String RULE_NAME = "andRight";

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
    protected TermParameter getDefaultOnParameter(ProofNode target) throws RuleException {
        return RuleUtil.schemaSequentParameter(target, "|- _ && _");
    }

    @Override
    public ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        Term on = parameters.getValue(ON_PARAM_OPT).getTerm();
        TermSelector selector = parameters.getValue(ON_PARAM_OPT).getTermSelector();
        ImmutableList<String> labels = selector.selectTopterm(target.getSequent()).getLabels();

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
                .addReplacement(selector, on.getTerm(0))
                .setLabel("case 1");


        builder.newBranch()
                .addReplacement(selector, on.getTerm(1))
                .setLabel("case 2");

      /*  builder.newBranch()
                .addDeletionsSuccedent(target.getSequent().getSuccedent().get(no))
                .addAdditionsSuccedent(new ProofFormula(on.getTerm(0)))
                .setLabel("case 1");

        builder.newBranch()
                .addDeletionsSuccedent(target.getSequent().getSuccedent().get(no))
                .addAdditionsSuccedent(new ProofFormula(on.getTerm(1), labels))
                .setLabel("case 2");*/

        builder.setApplicability(Applicability.APPLICABLE);

        return builder.build();
    }
}
