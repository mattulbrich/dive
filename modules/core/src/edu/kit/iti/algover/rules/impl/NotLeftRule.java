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
import edu.kit.iti.algover.script.callhandling.BuiltinCommands;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.match.Matching;
import edu.kit.iti.algover.term.match.SequentMatcher;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.RuleUtil;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;

/**
 * Created by jklamroth on 1/11/18.
 */
public class NotLeftRule extends AbstractProofRule {

    public NotLeftRule() {
        super(ON_PARAM);
    }

    @Override
    public String getName() {
        return "notLeft";
    }

    @Override
    public String getCategory() {
        return ProofRuleCategories.PROPOSITIONAL;
    }

    @Override
    public ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);

        TermParameter onParam = parameters.getValue(ON_PARAM);
        TermSelector selector = onParam.getTermSelector();

        if(!selector.isToplevel()) {
            throw NotApplicableException.onlyToplevel(this);
        }

        // TODO @Jonas: I added this check. I think it was missing. Right?
        if (!selector.isAntecedent()) {
            throw NotApplicableException.onlyAntecedent(this);
        }

        Term term = onParam.getTerm();
        if (!(term instanceof ApplTerm)) {
            throw NotApplicableException.onlyOperator(this, "!");
        }

        // TODO @Jonas: I added this check. I think it was missing. Right?
        ApplTerm at = (ApplTerm)term;
        if(at.getFunctionSymbol() != BuiltinSymbols.NOT) {
            throw NotApplicableException.onlyOperator(this, "!");
        }

        builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);

        /*try {
            // TODO @Jonas: This seems to not remove a negation but to add one
            // Is this intended?
            builder.newBranch().addDeletionsAntecedent(new ProofFormula(term))
                    .addAdditionsSuccedent(new ProofFormula(new ApplTerm(BuiltinSymbols.NOT, term)));

        } catch(TermBuildException e) {
            throw new RuleException(e);
        }*/
        builder.newBranch().addDeletionsAntecedent(new ProofFormula(term))
                .addAdditionsSuccedent(new ProofFormula(term.getTerm(0)));

        return builder.build();
    }

}
