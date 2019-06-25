/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules.impl;

import de.uka.ilkd.pp.NoExceptions;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.DefaultFocusProofRule;
import edu.kit.iti.algover.rules.NoFocusProofRule;
import edu.kit.iti.algover.rules.NotApplicableException;
import edu.kit.iti.algover.rules.ParameterDescription;
import edu.kit.iti.algover.rules.ParameterType;
import edu.kit.iti.algover.rules.Parameters;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.ProofRuleApplication.Applicability;
import edu.kit.iti.algover.rules.ProofRuleApplicationBuilder;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermParameter;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.rules.TermSelector.SequentPolarity;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.DefaultTermVisitor;
import edu.kit.iti.algover.term.QuantTerm;
import edu.kit.iti.algover.term.QuantTerm.Quantifier;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.term.builder.ReplacementVisitor;
import edu.kit.iti.algover.term.builder.TermBuildException;

/**
 * Created by jklamroth on 10/25/18.
 */
public class QuantifierInstantiation extends NoFocusProofRule {

    public static final ParameterDescription<TermParameter> WITH_PARAM =
            new ParameterDescription<>("with", ParameterType.TERM, true);

    public static final ParameterDescription<String> VAR_PARAM =
            new ParameterDescription<>("var", ParameterType.STRING, false);

    public QuantifierInstantiation() {
        super(DefaultFocusProofRule.ON_PARAM, WITH_PARAM);
    }

    @Override
    public String getName() {
        return "inst";
    }

    @Override
    protected ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {

        TermParameter onParam = parameters.getValue(DefaultFocusProofRule.ON_PARAM);
        TermParameter withParam = parameters.getValue(WITH_PARAM);

        if(onParam == null) {
            String varParm = parameters.getValue(VAR_PARAM);
            onParam = inferOnParam(varParm, target.getSequent());
        }
        
        Term onTerm = onParam.getTerm();
        if (!(onTerm instanceof QuantTerm)) {
            throw new NotApplicableException(getName() + " can only be applied to quantified formulas");
        }

        TermSelector onSel = onParam.getTermSelector();
        if (!onSel.isToplevel()) {
            throw NotApplicableException.onlyToplevel(this);
        }

        // Only antecedental forall and succedental exists can be instantiated
        Quantifier q = onSel.isAntecedent() ? Quantifier.FORALL : Quantifier.EXISTS;

        QuantTerm aTerm = (QuantTerm)onTerm;
        if(aTerm.getQuantifier() != q) {
            throw new NotApplicableException("Only forall quantifiers in antecedent or exists quantifiers in succedent can be instantiated");
        }

        ProofRuleApplicationBuilder pra = new ProofRuleApplicationBuilder(this);

        if(withParam == null) {
            pra.setApplicability(Applicability.INSTANTIATION_REQUIRED);
            return pra.build();
        }

        // REVIEW: Does it make sense to forbid bounded versions of the bound
        // variable?
        if (withParam.getTerm().accept(new ContainsVarVisitor(), aTerm.getBoundVar())) {
            throw new NotApplicableException("A quantifier cannot be instantiated with a term" +
                    " that contains the bound variable of the quantifier.");
        }

        if (!withParam.getTerm().getSort().isSubtypeOf(aTerm.getBoundVar().getSort())) {
            throw new NotApplicableException("The instantiated type is not compatible with the quantifier");
        }

        ReplaceBoundVisitor rv = new ReplaceBoundVisitor(withParam.getTerm(), aTerm.getBoundVar());
        Term rt = null;
        try {
            rt = onTerm.getTerm(0).accept(rv, null);
        } catch (TermBuildException e) {
            throw new RuleException("Could not instantiate quantifier.");
        }

        if(rt == null) {
            ProofRuleApplicationBuilder prab = new ProofRuleApplicationBuilder(this);
            prab.newBranch().addReplacement(onParam.getTermSelector(), onTerm.getTerm(0));
            return prab.build();
        }
        ProofRuleApplicationBuilder prab = new ProofRuleApplicationBuilder(this);
        prab.newBranch().addReplacement(onParam.getTermSelector(), rt);

        return prab.build();
    }

    private TermParameter inferOnParam(String varParm, Sequent sequent) throws NotApplicableException {
        TermSelector cand = null;

        int no = 0;
        for (ProofFormula formula : sequent.getAntecedent()) {
            if (formula.getTerm() instanceof QuantTerm) {
                QuantTerm qTerm = (QuantTerm) formula.getTerm();
                if (qTerm.getQuantifier() == Quantifier.FORALL &&
                        (varParm == null || qTerm.getBoundVar().getName().equals(varParm))) {
                    if(cand != null) {
                        throw new NotApplicableException("The instantiation context is not unique");
                    }
                    cand = new TermSelector(SequentPolarity.ANTECEDENT, no);
                }
            }
            no ++;
        }

        no = 0;
        for (ProofFormula formula : sequent.getSuccedent()) {
            if (formula.getTerm() instanceof QuantTerm) {
                QuantTerm qTerm = (QuantTerm) formula.getTerm();
                if (qTerm.getQuantifier() == Quantifier.EXISTS &&
                        (varParm == null || qTerm.getBoundVar().getName().equals(varParm))) {
                    if(cand != null) {
                        throw new NotApplicableException("The instantiation context is not unique");
                    }
                    cand = new TermSelector(SequentPolarity.SUCCEDENT, no);
                }
            }
            no ++;
        }

        if (cand == null) {
            throw new NotApplicableException("No instantiation context");
        }

        return new TermParameter(cand, sequent);
    }

    private static class ReplaceBoundVisitor extends ReplacementVisitor<Void> {
        private final Term replaceTerm;
        private final VariableTerm boundVariable;

        public ReplaceBoundVisitor(Term rt, VariableTerm vt) {
            replaceTerm = rt;
            boundVariable = vt;
        }

        @Override
        public Term visit(VariableTerm variableTerm, Void arg) throws TermBuildException {
            if(variableTerm.equals(boundVariable)) {
                return replaceTerm;
            }
            return super.visit(variableTerm, arg);
        }
    }

    private static class ContainsVarVisitor extends DefaultTermVisitor<VariableTerm, Boolean, NoExceptions> {
        @Override
        protected Boolean defaultVisit(Term term, VariableTerm arg) throws NoExceptions {
            if(term.equals(arg)) {
                return true;
            }
            if(term instanceof ApplTerm
                    && ((ApplTerm) term).getFunctionSymbol().getName().equals(arg.getName())
                    && term.getSubterms().size() == 0) {
                return true;
            }
            for(Term t : term.getSubterms()) {
                if(defaultVisit(t, arg)) {
                    return true;
                }
            }
            return false;
        }
    }
}
