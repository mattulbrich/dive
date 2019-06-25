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
import edu.kit.iti.algover.term.builder.TermBuildException;

/**
 * Created by jklamroth on 5/22/18.
 *
 * TODO Document
 */
public class ModusTollensRule extends FocusProofRule {
    public ModusTollensRule() {
        super(ON_PARAM);
    }

    @Override
    public String getName() {
        return "modusTollens";
    }

    @Override
    public String getCategory() {
        return ProofRuleCategories.PROPOSITIONAL;
    }

    @Override
    protected ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        TermSelector selector = parameters.getValue(ON_PARAM).getTermSelector();
        Term term = parameters.getValue(ON_PARAM).getTerm();

        if (!(term instanceof ApplTerm)) {
            throw NotApplicableException.onlyOperator(this, "==>");
        }

        if (!selector.isToplevel()) {
            throw NotApplicableException.onlyToplevel(this);
        }

        ApplTerm appl = (ApplTerm) term;
        FunctionSymbol fs = appl.getFunctionSymbol();

        if (fs != BuiltinSymbols.IMP) {
            throw NotApplicableException.onlyOperator(this, "!");
        }

        Term notTerm;

        try {
            notTerm = new ApplTerm(BuiltinSymbols.NOT, appl.getTerm(1));
        } catch (TermBuildException e) {
            throw new RuleException("Failed to build negated term.", e);
        }

        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);
        Term notTerm2;
        try {
            notTerm2 = new ApplTerm(BuiltinSymbols.NOT, appl.getTerm(0));
        } catch (TermBuildException e) {
            throw new RuleException("Failed to build negated term.", e);
        }

        builder.newBranch().addReplacement(selector, notTerm2).setLabel("mainBranch");
        BranchInfoBuilder b = builder.newBranch();
        for(ProofFormula pf : target.getSequent().getSuccedent()) {
            b.addDeletionsSuccedent(pf);
        }
        b.addAdditionsSuccedent(new ProofFormula(notTerm)).setLabel("assumption");
        builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);

        return builder.build();
    }
}
