package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.util.RuleUtil;

/**
 * Created by jklamroth on 5/16/18.
 */
public class CutRule extends AbstractProofRule {
    private static final ParameterDescription<Term> WITH_PARAM = new ParameterDescription<>("with", ParameterType.TERM, true);

    public CutRule () {
        super(WITH_PARAM);
    }

    @Override
    public String getName() {
        return "cut";
    }

    @Override
    protected ProofRuleApplication considerApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        return apply(target, parameters);
    }

    @Override
    protected ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        return apply(target, parameters);
    }

    private ProofRuleApplication apply(ProofNode target, Parameters parameters) throws RuleException {
        Term with = parameters.getValue(WITH_PARAM);
        ProofRuleApplicationBuilder pra = new ProofRuleApplicationBuilder(this);
        pra.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);
        pra.newBranch().addAdditionAntecedent(new ProofFormula(with)).setLabel("case 1");
        try {
            pra.newBranch().addAdditionAntecedent(new ProofFormula(new ApplTerm(BuiltinSymbols.NOT, with))).setLabel("case 2");
        } catch (TermBuildException e) {
            throw new RuleException("Could not create negated cut term.", e);
        }
        return pra.build();
    }
}
