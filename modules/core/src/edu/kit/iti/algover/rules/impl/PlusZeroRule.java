/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.AbstractProofRule;
import edu.kit.iti.algover.rules.Parameters;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.ProofRuleApplicationBuilder;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermParameter;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuildException;

/**
 * Created by jklamroth on 11/7/18.
 */
public class PlusZeroRule extends AbstractProofRule {

    public PlusZeroRule() {
        super(ON_PARAM);
    }

    @Override
    public String getName() {
        return "plus0";
    }

    @Override
    public ProofRuleApplication considerApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        TermParameter onParam = parameters.getValue(ON_PARAM);
        if(onParam == null) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }
        Term onTerm = onParam.getTerm();
        if(!(onTerm instanceof ApplTerm)) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        ApplTerm applTerm = (ApplTerm)onTerm;
        if(applTerm.getFunctionSymbol() != BuiltinSymbols.PLUS && applTerm.getFunctionSymbol() != BuiltinSymbols.MINUS) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        Term rt = null;
        try {
            if (applTerm.getTerm(0).equals(new ApplTerm(new FunctionSymbol("0", Sort.INT)))) {
                rt = applTerm.getTerm(1);
            }
            if (applTerm.getTerm(1).equals(new ApplTerm(new FunctionSymbol("0", Sort.INT)))) {
                rt = applTerm.getTerm(0);
            }
        } catch (TermBuildException e) {
            throw new RuleException("This should not happen. Error building constants in PlusZeroRule.");
        }
        if(rt == null) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        ProofRuleApplicationBuilder prab = new ProofRuleApplicationBuilder(this);
        prab.newBranch().addReplacement(onParam.getTermSelector(), rt);
        return prab.build();
    }

    @Override
    protected ProofRuleApplication makeApplicationImpl_OLD(ProofNode target, Parameters parameters) throws RuleException {
        ProofRuleApplication pra = considerApplicationImpl(target, parameters);
        if(pra.getApplicability() != ProofRuleApplication.Applicability.APPLICABLE) {
            throw new RuleException("PlusZeroRule is not applicable in make");
        }
        return pra;
    }
}
