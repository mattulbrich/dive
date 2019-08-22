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
import edu.kit.iti.algover.term.ReferenceTerm;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.RuleUtil;

/**
 * Created by jklamroth on 5/22/18.
 */
public class AndLeftRule extends DefaultFocusProofRule {

    @Override
    public boolean mayBeExhaustive() {
        return true;
    }

    @Override
    public String getName() {
        return "andLeft";
    }

    @Override
    public String getCategory() {
        return ProofRuleCategories.PROPOSITIONAL;
    }

    @Override
    protected TermParameter getDefaultOnParameter(ProofNode target) throws RuleException {
        return RuleUtil.schemaSequentParameter(target, "_ && _ |-");
    }

    @Override
    protected ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {

        TermSelector selector = parameters.getValue(ON_PARAM).getTermSelector();

        if(!selector.isToplevel()) {
            throw NotApplicableException.onlyToplevel(this);
        }
        if(!selector.isAntecedent()) {
            throw NotApplicableException.onlyAntecedent(this);
        }

        ProofFormula formula = selector.selectTopterm(target.getSequent());
        Term term = formula.getTerm();
        if (!(term instanceof ApplTerm)) {
            throw NotApplicableException.onlyOperator(this, "&&");
        }
        ApplTerm appl = (ApplTerm) term;
        FunctionSymbol fs = appl.getFunctionSymbol();

        if (fs != BuiltinSymbols.AND) {
            throw NotApplicableException.onlyOperator(this, "&&");
        }

        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);

        builder.newBranch().
                addDeletions(Sequent.singleAntecedent(formula)).
                addAdditionAntecedent(new ProofFormula(new ReferenceTerm(selector.selectSubterm(0)), formula.getLabels())).
                addAdditionAntecedent(new ProofFormula(new ReferenceTerm(selector.selectSubterm(1)), formula.getLabels()));

        builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);

        return builder.build();
    }
}
