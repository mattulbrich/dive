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
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.match.Matching;
import edu.kit.iti.algover.term.match.SequentMatcher;
import edu.kit.iti.algover.term.match.TermMatcher;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.RuleUtil;

import java.util.List;
import java.util.Optional;

/**
 * Created by jklamroth on 5/22/18.
 */

//REVIEW . @Jonas. Is this really modus ponens?! Is it rather some kind of impLeft


public class ModusPonensRule extends AbstractProofRule {
    public ModusPonensRule() {
        super(ON_PARAM);
    }

    @Override
    public String getName() {
        return "modusPonens";
    }

    @Override
    public String getCategory() {
        return ProofRuleCategories.PROPOSITIONAL;
    }

    @Override
    protected ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        TermSelector selector = parameters.getValue(ON_PARAM).getTermSelector();

        ProofFormula formula = selector.selectTopterm(target.getSequent());
        Term term = formula.getTerm();
        if (!(term instanceof ApplTerm)) {
            throw new NotApplicableException("Modus Ponens is only applicable on implications.");
        }
        ApplTerm appl = (ApplTerm) term;
        FunctionSymbol fs = appl.getFunctionSymbol();

        if (fs != BuiltinSymbols.IMP) {
            throw new NotApplicableException("Modus Ponens is only applicable on implications.");
        }

        // TODO @Jonas. Should there not be a check for antecedent (or succedent?!)
        // TODO @Jonas. Should there not be a check for toplevel?

        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);

        builder.newBranch().addReplacement(selector, appl.getTerm(1)).setLabel("mainBranch");
        builder.newBranch().addDeletionsSuccedent(target.getSequent().getSuccedent()).
                addAdditionsSuccedent(new ProofFormula(appl.getTerm(0))).setLabel("assumption");
        builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);

        return builder.build();
    }
}
