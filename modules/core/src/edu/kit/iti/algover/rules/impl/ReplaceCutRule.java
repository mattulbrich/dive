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
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.builder.TermBuilder;

/**
 * Created by jklamroth on 7/25/18.
 */
public class ReplaceCutRule extends AbstractProofRule {
    private static final ParameterDescription<Term> WITH_PARAM = new ParameterDescription<>("with", ParameterType.TERM, true);
    private static final ParameterDescription<Boolean> AUTO_PARAM = new ParameterDescription<>("auto", ParameterType.BOOLEAN, false);
    public ReplaceCutRule() {
        super(ON_PARAM, WITH_PARAM, AUTO_PARAM);
    }

    public String getName() {
        return "replace";
    }

    @Override
    protected ProofRuleApplication considerApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        Term with = parameters.getValue(WITH_PARAM);
        Term on = parameters.getValue(ON_PARAM);

        if(with == null || on == null) {
            ProofRuleApplicationBuilder pra = new ProofRuleApplicationBuilder(this);
            pra.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);
            return pra.build();
        }

        TermSelector selector = tsForParameter.get("on");

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
        Term with = parameters.getValue(WITH_PARAM);
        Term on = parameters.getValue(ON_PARAM);

        if(with == null || on == null) {
            throw new RuleException("With or on null");
        }

        TermSelector selector = tsForParameter.get("on");

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
