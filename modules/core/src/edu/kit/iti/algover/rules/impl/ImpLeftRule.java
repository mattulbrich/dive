/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.match.Matching;
import edu.kit.iti.algover.term.match.SequentMatcher;
import edu.kit.iti.algover.term.match.TermMatcher;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.RuleUtil;

import java.util.List;
import java.util.Optional;

/**
 * Created by jklamroth on 5/22/18.
 */

public class ImpLeftRule extends DefaultFocusProofRule {
    @Override
    public String getName() {
        return "impLeft";
    }

    @Override
    public String getCategory() {
        return ProofRuleCategories.PROPOSITIONAL;
    }

    @Override
    protected TermParameter getDefaultOnParameter(ProofNode target) throws RuleException {
        return RuleUtil.schemaSequentParameter(target, "_ ==> _ |-");
    }

    @Override
    protected ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        TermSelector selector = parameters.getValue(ON_PARAM_OPT).getTermSelector();

        ProofFormula formula = selector.selectTopterm(target.getSequent());
        Term term = formula.getTerm();
        if (!(term instanceof ApplTerm)) {
            throw NotApplicableException.onlyOperator(this, "==>");
        }
        ApplTerm appl = (ApplTerm) term;
        FunctionSymbol fs = appl.getFunctionSymbol();

        if (fs != BuiltinSymbols.IMP) {
            throw NotApplicableException.onlyOperator(this, "==>");
        }

        if(!selector.isToplevel()) {
            throw NotApplicableException.onlyToplevel(this);
        }

        if(!selector.isAntecedent()) {
            throw NotApplicableException.onlyAntecedent(this);
        }

        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);

        builder.newBranch().addReplacement(selector, appl.getTerm(1)).setLabel("mainBranch");
        Term pf = null;
        try {
            pf = new ApplTerm(BuiltinSymbols.NOT, appl.getTerm(0));
        } catch (TermBuildException tbe) {
            throw new RuleException("Error creating negated term in impLeft-Rule.");
        }
        builder.newBranch().addReplacement(selector, pf);

        builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);

        return builder.build();
    }
}
