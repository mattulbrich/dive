package edu.kit.iti.algover.rules.impl;

import de.uka.ilkd.pp.NoExceptions;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.AbstractProofRule;
import edu.kit.iti.algover.rules.ParameterDescription;
import edu.kit.iti.algover.rules.ParameterType;
import edu.kit.iti.algover.rules.Parameters;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.ProofRuleApplicationBuilder;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermParameter;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.DefaultTermVisitor;
import edu.kit.iti.algover.term.QuantTerm;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.term.builder.ReplaceVisitor;
import edu.kit.iti.algover.term.builder.ReplacementVisitor;
import edu.kit.iti.algover.term.builder.TermBuildException;

/**
 * Created by jklamroth on 10/25/18.
 */
public class QuantifierInstantiation extends AbstractProofRule {
    private static final ParameterDescription<TermParameter> WITH_PARAM = new ParameterDescription<>("with", ParameterType.TERM, true);

    public QuantifierInstantiation() {
        super(ON_PARAM, WITH_PARAM);
    }

    @Override
    public String getName() {
        return "forallInstantiation";
    }

    @Override
    protected ProofRuleApplication considerApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        TermParameter onParam = parameters.getValue(ON_PARAM);
        TermParameter withParam = parameters.getValue(WITH_PARAM);
        QuantTerm aTerm;
        Term onTerm;

        if(onParam == null) {
            ProofRuleApplicationBuilder pra = new ProofRuleApplicationBuilder(this);
            pra.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);
            return pra.build();
        } else {
            onTerm = onParam.getTerm();
            if(!(onTerm instanceof QuantTerm)) {
                return ProofRuleApplicationBuilder.notApplicable(this);
            }

            aTerm = (QuantTerm)onTerm;
            if(aTerm.getQuantifier() != QuantTerm.Quantifier.FORALL) {
                return ProofRuleApplicationBuilder.notApplicable(this);
            }
        }

        if(withParam == null) {
            ProofRuleApplicationBuilder pra = new ProofRuleApplicationBuilder(this);
            pra.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);
            return pra.build();
        }


        assert(onTerm != null);
        assert(aTerm != null);
        if(withParam.getTerm().accept(new ContainsVarVisitor(), aTerm.getBoundVar())) {
            return ProofRuleApplicationBuilder.notApplicable(this);
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

    @Override
    protected ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        ProofRuleApplication pra = considerApplicationImpl(target, parameters);
        if(pra.getApplicability() != ProofRuleApplication.Applicability.APPLICABLE) {
            throw new RuleException("Rule " + getName() + " is not applicable on sequent " + target.getSequent());
        }
        return pra;
    }

    class ReplaceBoundVisitor extends ReplacementVisitor<Void> {
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

    class ContainsVarVisitor extends DefaultTermVisitor<VariableTerm, Boolean, NoExceptions> {
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
