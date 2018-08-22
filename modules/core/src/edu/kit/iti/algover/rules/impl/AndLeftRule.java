package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.match.Matching;
import edu.kit.iti.algover.term.match.SequentMatcher;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.RuleUtil;

import java.util.List;

/**
 * Created by jklamroth on 5/22/18.
 */
public class AndLeftRule extends AbstractProofRule {
    public AndLeftRule() {
        super(ON_PARAM);
    }

    @Override
    public String getName() {
        return "andLeft";
    }

    @Override
    protected ProofRuleApplication considerApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        TermSelector selector = tsForParameter.get("on");

        if(!selector.isToplevel()) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }
        if(!selector.isAntecedent()) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        ProofFormula formula = selector.selectTopterm(target.getSequent());
        Term term = formula.getTerm();
        if (!(term instanceof ApplTerm)) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }
        ApplTerm appl = (ApplTerm) term;
        FunctionSymbol fs = appl.getFunctionSymbol();

        if (fs != BuiltinSymbols.AND) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);

        builder.newBranch().addReplacement(selector, appl.getTerm(0)).
                addAdditionAntecedent(new ProofFormula(appl.getTerm(1)));
        builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);

        return builder.build();
    }

    @Override
    protected ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        Term on = parameters.getValue(ON_PARAM);
        List<TermSelector> l = RuleUtil.matchSubtermsInSequent(on::equals, target.getSequent());
        if(l.size() != 1) {
            throw new RuleException("Matching of on parameter is ambiguous.");
        }
        TermSelector selector = l.get(0);
        if(!selector.isToplevel()) {
            throw new RuleException("andLeft may only be applied to TopLevel terms.");
        }
        if(!selector.isAntecedent()) {
            throw new RuleException("andLeft may only be applied on the antecedent.");
        }

        ProofFormula formula = selector.selectTopterm(target.getSequent());
        Term term = formula.getTerm();
        if (!(term instanceof ApplTerm)) {
            throw new RuleException("andLeft may only be applied to or terms.");
        }
        ApplTerm appl = (ApplTerm) term;
        FunctionSymbol fs = appl.getFunctionSymbol();

        if (fs != BuiltinSymbols.AND) {
            throw new RuleException("andLeft may only be applied to or terms.");
        }

        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);

        builder.newBranch().addReplacement(selector, appl.getTerm(0)).
                addAdditionAntecedent(new ProofFormula(appl.getTerm(1)));
        builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);

        return builder.build();
    }
}
