/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.rules.ProofRuleApplication.Applicability;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.builder.TermBuilder;

import java.util.Set;

/**
 * Created by jklamroth on 7/25/18.
 */
public class ReplaceCutRule extends FocusProofRule {

    private static final ParameterDescription<TermParameter> WITH_PARAM =
            new ParameterDescription<>("with", ParameterType.TERM, true);


    private static final ParameterDescription<Boolean> AUTO_PARAM =
            new ParameterDescription<>("auto", ParameterType.BOOLEAN, false);

    public ReplaceCutRule() {
        super(WITH_PARAM, AUTO_PARAM);
    }

    public String getName() {
        return "replace";
    }

    @Override
    public String getCategory() {
        return ProofRuleCategories.SIMPLIFICATIONS;
    }

    @Override
    protected ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        TermParameter withParam = parameters.getValue(WITH_PARAM);

        if(withParam == null) {
            ProofRuleApplicationBuilder pra = new ProofRuleApplicationBuilder(this);
            pra.setApplicability(Applicability.INSTANTIATION_REQUIRED);
            return pra.build();
        }

        TermParameter onParam = parameters.getValue(ON_PARAM_REQ);
        Term on = onParam.getTerm();
        Term with = withParam.getTerm();

        TermSelector selector = parameters.getValue(ON_PARAM_REQ).getTermSelector();

        if(!on.getSort().equals(with.getSort())) {
            throw new NotApplicableException("Found type " + with.getSort().toString() + " as replacement but original term has type "
             + on.getSort().toString() + " (has to be the same type).");
        }

        ProofRuleApplicationBuilder pra = new ProofRuleApplicationBuilder(this);
        pra.newBranch().addReplacement(selector, with).setLabel("replace");
        TermBuilder tb = new TermBuilder(target.getAllSymbols());
        try {
            // Probably universal closure is required here.
            Set<VariableTerm> freeVars = FreeVarVisitor.findFreeVars(on);
            if(!freeVars.isEmpty()) {
                throw new NotApplicableException("The replacement-Term may not contain free variables.");
            }
            Term justificationTerm = tb.eq(on, with);
            pra.newBranch().addAdditionsSuccedent(new ProofFormula(justificationTerm)).setLabel("justification");
        } catch (TermBuildException e) {
            throw new RuleException("Error building justification term: " + e.getMessage(), e);
        }

        // TODO: auto parameter!

       /* pra.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);
        pra.newBranch().addReplacement(selector, with).setLabel("replace");
*/
        return pra.build();
    }

}
