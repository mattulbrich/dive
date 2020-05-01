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
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.RuleUtil;

/**
 * Created by jklamroth on 1/11/18.
 */
public class NotLeftRule extends DefaultFocusProofRule {

    @Override
    public String getName() {
        return "notLeft";
    }

    @Override
    public String getCategory() {
        return ProofRuleCategories.PROPOSITIONAL;
    }

    @Override
    protected TermParameter getDefaultOnParameter(ProofNode target) throws RuleException {
        return RuleUtil.schemaSequentParameter(target, "!_ |-");
    }

    @Override
    public ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);

        TermParameter onParam = parameters.getValue(ON_PARAM_OPT);
        TermSelector selector = onParam.getTermSelector();

        if(!selector.isToplevel()) {
            throw NotApplicableException.onlyToplevel(this);
        }

        if (!selector.isAntecedent()) {
            throw NotApplicableException.onlyAntecedent(this);
        }

        Term term = onParam.getTerm();
        if (!(term instanceof ApplTerm)) {
            throw NotApplicableException.onlyOperator(this, "!");
        }

        ApplTerm at = (ApplTerm)term;
        if(at.getFunctionSymbol() != BuiltinSymbols.NOT) {
            throw NotApplicableException.onlyOperator(this, "!");
        }

        builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);

        builder.newBranch().addDeletionsAntecedent(new ProofFormula(term))
                .addAdditionsSuccedent(new ProofFormula(term.getTerm(0)));

        return builder.build();
    }

}
