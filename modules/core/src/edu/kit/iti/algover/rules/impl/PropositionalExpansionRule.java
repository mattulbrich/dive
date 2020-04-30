/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules.impl;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Spliterator;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.NoFocusProofRule;
import edu.kit.iti.algover.rules.ParameterDescription;
import edu.kit.iti.algover.rules.ParameterType;
import edu.kit.iti.algover.rules.Parameters;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.ProofRuleApplication.Applicability;
import edu.kit.iti.algover.rules.ProofRuleApplicationBuilder;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.rules.TermSelector.SequentPolarity;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.match.Matching;
import edu.kit.iti.algover.term.match.SequentMatcher;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.RuleUtil;

// ALPHA ... Just for demo purposes so far.

public class PropositionalExpansionRule extends NoFocusProofRule {

    private static final ParameterDescription<Boolean> SPLT_PARAM =
            new ParameterDescription<>("split", ParameterType.BOOLEAN, false);

    public PropositionalExpansionRule() {
        super(SPLT_PARAM);
    }

    @Override
    public String getCategory() {
        return ProofRuleCategories.PROPOSITIONAL;
    }

    @Override
    public String getName() {
        return "prop";
    }

    @Override
    public ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        // TODO: Make this a parameter
        boolean allowSplit = parameters.getValueOrDefault(SPLT_PARAM, true);

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

        int caseNo = 0;
        for (Sequent sequent : sequents) {
            builder.newBranch().addAdditions(sequent)
                    .addDeletionsAntecedent(deletionsAnte)
                    .addDeletionsSuccedent(deletionsSucc).setLabel("case " + ++caseNo);
        }

        builder.setApplicability(Applicability.APPLICABLE);

        return builder.build();
    }

}
