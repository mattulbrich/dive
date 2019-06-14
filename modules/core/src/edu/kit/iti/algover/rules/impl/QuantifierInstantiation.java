/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules.impl;

import de.uka.ilkd.pp.NoExceptions;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.AbstractProofRule;
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
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.DefaultTermVisitor;
import edu.kit.iti.algover.term.QuantTerm;
import edu.kit.iti.algover.term.QuantTerm.Quantifier;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.term.builder.ReplaceVisitor;
import edu.kit.iti.algover.term.builder.ReplacementVisitor;
import edu.kit.iti.algover.term.builder.TermBuildException;

/**
 * Created by jklamroth on 10/25/18.
 */
// REVIEW @Jonas: The name suggests that this for all instantiations, yet
// the name is for forall-left only.
public class QuantifierInstantiation extends AbstractProofRule {
    public static final ParameterDescription<TermParameter> WITH_PARAM =
            new ParameterDescription<>("with", ParameterType.TERM, true);

    public QuantifierInstantiation() {
        super(ON_PARAM, WITH_PARAM);
    }

    @Override
    public String getName() {
        //  REVIEW @Jonas: I suggest "inst" only
        return "forallInstantiation";
    }

    @Override
    protected ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {

        TermParameter onParam = parameters.getValue(ON_PARAM);
        TermParameter withParam = parameters.getValue(WITH_PARAM);

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
        // variable.
        if (withParam.getTerm().accept(new ContainsVarVisitor(), aTerm.getBoundVar())) {
            // TODO @Jonas, please report the right error message here.
            throw new NotApplicableException("XXX The instantiation contains variables");
        }

        if (!withParam.getTerm().getSort().isSubtypeOf(aTerm.getBoundVar().getSort())) {
            throw new NotApplicableException("The instantiated type is not compatible with the quantifer");
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
