/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules.impl;

import java.util.ArrayList;
import java.util.List;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.AbstractProofRule;
import edu.kit.iti.algover.rules.Parameters;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.ProofRuleApplication.Applicability;
import edu.kit.iti.algover.rules.ProofRuleApplicationBuilder;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.rules.TermSelector.SequentPolarity;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.RuleUtil;

// ALPHA ... Just for demo purposes so far.

public class PropositionalExpansionRule extends AbstractProofRule {

    public PropositionalExpansionRule() {
        super(ON_PARAM);
    }

    @Override
    public String getName() {
        return "prop-expand";
    }

    @Override
    public ProofRuleApplication considerApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        TermSelector selector = parameters.getValue(ON_PARAM).getTermSelector();

        if (selector != null) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        boolean allowSplit = true;

        PropositionalExpander pex = new PropositionalExpander();
        List<ProofFormula> deletionsAnte = new ArrayList<ProofFormula>();
        List<ProofFormula> deletionsSucc = new ArrayList<ProofFormula>();

        for (ProofFormula formula : target.getSequent().getAntecedent()) {
            if (pex.expand(formula, SequentPolarity.ANTECEDENT, allowSplit)) {
                deletionsAnte.add(formula);
            }
        }

        for (ProofFormula formula : target.getSequent().getSuccedent()) {
            if (pex.expand(formula, SequentPolarity.SUCCEDENT, allowSplit)) {
                deletionsSucc.add(formula);
            }
        }

        List<Sequent> sequents = pex.getSequents();

        if (deletionsAnte.isEmpty() && deletionsSucc.isEmpty()) {
            // nothing to be done
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);

        for (Sequent sequent : sequents) {
            builder.newBranch().addAdditions(sequent)
                    .addDeletionsAntecedent(deletionsAnte)
                    .addDeletionsSuccedent(deletionsSucc);
        }

        builder.setApplicability(Applicability.APPLICABLE);

        return builder.build();
    }

    @Override
    public ProofRuleApplication makeApplicationImpl_OLD(ProofNode target, Parameters parameters) throws RuleException {
        //TODO just copy and pasted from considerApplicationImpl maybe correct or improve
        Term on = parameters.getValue(ON_PARAM).getTerm();
        List<TermSelector> l = RuleUtil.matchSubtermsInSequent(on::equals, target.getSequent());
        if(l.size() != 1) {
            throw new RuleException("Matching of on parameter is ambiguous");
        }
        TermSelector selector = l.get(0);
        if (selector != null) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        boolean allowSplit = true;

        PropositionalExpander pex = new PropositionalExpander();
        List<ProofFormula> deletionsAnte = new ArrayList<ProofFormula>();
        List<ProofFormula> deletionsSucc = new ArrayList<ProofFormula>();

        for (ProofFormula formula : target.getSequent().getAntecedent()) {
            if (pex.expand(formula, SequentPolarity.ANTECEDENT, allowSplit)) {
                deletionsAnte.add(formula);
            }
        }

        for (ProofFormula formula : target.getSequent().getSuccedent()) {
            if (pex.expand(formula, SequentPolarity.SUCCEDENT, allowSplit)) {
                deletionsSucc.add(formula);
            }
        }

        List<Sequent> sequents = pex.getSequents();

        if (deletionsAnte.isEmpty() && deletionsSucc.isEmpty()) {
            // nothing to be done
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);

        for (Sequent sequent : sequents) {
            builder.newBranch().addAdditions(sequent)
                    .addDeletionsAntecedent(deletionsAnte)
                    .addDeletionsSuccedent(deletionsSucc);
        }

        builder.setApplicability(Applicability.APPLICABLE);

        return builder.build();
    }

}
