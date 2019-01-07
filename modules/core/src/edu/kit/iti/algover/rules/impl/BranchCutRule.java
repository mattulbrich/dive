package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.AbstractProofRule;
import edu.kit.iti.algover.rules.ParameterDescription;
import edu.kit.iti.algover.rules.ParameterType;
import edu.kit.iti.algover.rules.Parameters;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.ProofRuleApplicationBuilder;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermParameter;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuildException;

/**
 * Created by jklamroth on 10/31/18.
 */
public class BranchCutRule extends AbstractProofRule {
    private static final ParameterDescription<TermParameter> WITH_PARAM = new ParameterDescription<>("with", ParameterType.TERM, true);

    public BranchCutRule() {
        super(WITH_PARAM);
    }

    @Override
    public String getName() {
        return "branchCut";
    }

    @Override
    protected ProofRuleApplication considerApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        TermParameter withParam = parameters.getValue(WITH_PARAM);

        if(withParam == null) {
            ProofRuleApplicationBuilder pra = new ProofRuleApplicationBuilder(this);
            pra.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);
            return pra.build();
        }
        Term with = withParam.getTerm();
        if(with.getSort() != Sort.BOOL) {
            throw new RuleException("Cut term has to have type bool but has type " + with.getSort() + ".");
        }
        ProofRuleApplicationBuilder pra = new ProofRuleApplicationBuilder(this);
        pra.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);
        pra.newBranch().addAdditionAntecedent(new ProofFormula(with)).setLabel("add");
        try {
            pra.newBranch().addAdditionAntecedent(new ProofFormula(new ApplTerm(BuiltinSymbols.NOT, with))).setLabel("negatedAdd");
        } catch(TermBuildException e) {
            throw new RuleException("Could not create negated Term of " + with);
        }

        return pra.build();
    }

    @Override
    protected ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        return apply(target, parameters);
    }

    private ProofRuleApplication apply(ProofNode target, Parameters parameters) throws RuleException {
        Term with = parameters.getValue(WITH_PARAM).getTerm();

        if(with.getSort() != Sort.BOOL) {
            throw new RuleException("Cut term has to have type bool but has type " + with.getSort() + ".");
        }
        ProofRuleApplicationBuilder pra = new ProofRuleApplicationBuilder(this);
        pra.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);
        pra.newBranch().addAdditionAntecedent(new ProofFormula(with)).setLabel("add");
        try {
            pra.newBranch().addAdditionAntecedent(new ProofFormula(new ApplTerm(BuiltinSymbols.NOT, with))).setLabel("negatedAdd");
        } catch(TermBuildException e) {
            throw new RuleException("Could not create negated Term of " + with);
        }

        return pra.build();
    }

}
