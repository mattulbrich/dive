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
import edu.kit.iti.algover.util.RuleUtil;

import java.util.Optional;

/**
 * Created by jklamroth on 1/17/18.
 */
public class OrLeftRule extends AbstractProofRule {

    public OrLeftRule() {
        super(ON_PARAM);
    }

    @Override
    public boolean mayBeExhaustive() {
        return true;
    }

    @Override
    public String getName() {
        return "orLeft";
    }

    @Override
    public ProofRuleApplication considerApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        TermSelector selector = parameters.getValue(ON_PARAM).getTermSelector();

        if(selector == null || !selector.isToplevel() || selector.isSuccedent()) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }
        ProofFormula f = selector.selectTopterm(target.getSequent());
        Term t = f.getTerm();

        if(!(t instanceof ApplTerm)) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }
        ApplTerm at = (ApplTerm)t;
        if(at.getFunctionSymbol() != BuiltinSymbols.OR) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);
        builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);

        builder.newBranch().addReplacement(selector, at.getTerm(0)).setLabel("case 1");
        builder.newBranch().addReplacement(selector, at.getTerm(1)).setLabel("case 2");

        return builder.build();
    }

    @Override
    public ProofRuleApplication makeApplicationImpl_OLD(ProofNode target, Parameters parameters) throws RuleException {
        Term p = parameters.getValue(ON_PARAM).getTerm();
        if(!(p instanceof ApplTerm)) {
            throw new RuleException("orLeft has to be applied to an ApplicationTerm");
        }
        ApplTerm on = (ApplTerm)p;
        if(on.getFunctionSymbol() != BuiltinSymbols.OR) {
            throw new RuleException("orLeft has to be applied to a term with function symbol \"||\"");
        }
        if(Optional.empty().equals(RuleUtil.matchTopLevelInAntedecent(on::equals, target.getSequent()))) {
            throw new RuleException("orLeft can only be applied to a term in the antecedent");
        }


        Optional<TermSelector> ots = RuleUtil.matchSubtermInSequent(on::equals, target.getSequent());
        if(!ots.isPresent()) {
            throw new RuleException("on is ambiguos.");
        }
        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);
        builder.newBranch().addReplacement(ots.get(), on.getTerm(0)).setLabel("case 1");
        builder.newBranch().addReplacement(ots.get(), on.getTerm(1)).setLabel("case 2");

        return builder.build();
    }
}
