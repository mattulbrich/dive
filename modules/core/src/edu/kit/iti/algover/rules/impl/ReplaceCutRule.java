package edu.kit.iti.algover.rules.impl;

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
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.builder.TermBuilder;

/**
 * Created by jklamroth on 7/25/18.
 */
public class ReplaceCutRule extends AbstractProofRule {
    private static final ParameterDescription<TermParameter> WITH_PARAM = new ParameterDescription<>("with", ParameterType.TERM, true);
    private static final ParameterDescription<Boolean> AUTO_PARAM = new ParameterDescription<>("auto", ParameterType.BOOLEAN, false);
    public ReplaceCutRule() {
        super(ON_PARAM, WITH_PARAM, AUTO_PARAM);
    }

    public String getName() {
        return "replace";
    }

    @Override
    protected ProofRuleApplication considerApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        TermParameter withParam = parameters.getValue(WITH_PARAM);
        TermParameter onParam = parameters.getValue(ON_PARAM);

        if(withParam == null || onParam == null) {
            ProofRuleApplicationBuilder pra = new ProofRuleApplicationBuilder(this);
            pra.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);
            return pra.build();
        }

        Term on = onParam.getTerm();
        Term with = withParam.getTerm();

        TermSelector selector = parameters.getValue(ON_PARAM).getTermSelector();

        ProofRuleApplicationBuilder pra = new ProofRuleApplicationBuilder(this);
        pra.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);
        pra.newBranch().addReplacement(selector, with).setLabel("replace");
        TermBuilder tb = new TermBuilder(target.getPVC().getSymbolTable());
        Term justificationTerm = null;
        try {
            justificationTerm = tb.eq(on, with);
        } catch (TermBuildException e) {
            throw new RuleException("error building justification term.", e);
        }

        pra.newBranch().addAdditionsSuccedent(new ProofFormula(justificationTerm)).setLabel("justification");

        return pra.build();
    }

    @Override
    protected ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        Term with = parameters.getValue(WITH_PARAM).getTerm();
        Term on = parameters.getValue(ON_PARAM).getTerm();

        if(with == null || on == null) {
            throw new RuleException("With or on null");
        }

        TermSelector selector = parameters.getValue(ON_PARAM).getTermSelector();

        ProofRuleApplicationBuilder pra = new ProofRuleApplicationBuilder(this);
        pra.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);
        pra.newBranch().addReplacement(selector, with).setLabel("replace");
        TermBuilder tb = new TermBuilder(target.getPVC().getSymbolTable());
        Term justificationTerm = null;
        try {
            justificationTerm = tb.eq(on, with);
            pra.newBranch().addAdditionsSuccedent(new ProofFormula(justificationTerm)).
                    setLabel("justification");
        } catch (TermBuildException e) {
            throw new RuleException("error building justification term.", e);
        }

        return pra.build();
    }
}
