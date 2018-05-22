package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.util.RuleUtil;

import java.util.List;
import java.util.Optional;

/**
 * Created by jklamroth on 5/22/18.
 */
public class ModusTollensRule extends AbstractProofRule {
    public ModusTollensRule() {
        super(ON_PARAM);
    }

    @Override
    public String getName() {
        return "modusTollens";
    }

    @Override
    protected ProofRuleApplication considerApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        Term on = parameters.getValue(ON_PARAM);
        List<TermSelector> l = RuleUtil.matchSubtermsInSequent(on::equals, target.getSequent());
        if(l.size() != 1) {
            throw new RuleException("Matching of on parameter is ambiguous");
        }
        TermSelector selector = l.get(0);

        ProofFormula formula = selector.selectTopterm(target.getSequent());
        Term term = formula.getTerm();
        if (!(term instanceof ApplTerm)) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }
        ApplTerm appl = (ApplTerm) term;
        FunctionSymbol fs = appl.getFunctionSymbol();

        if (fs != BuiltinSymbols.IMP) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        Term notTerm;
        try {
            notTerm = new ApplTerm(BuiltinSymbols.NOT, appl.getTerm(1));
        } catch (TermBuildException e) {
            throw new RuleException("Failed to build negated term.", e);
        }

        Optional<Integer> ts = RuleUtil.matchTopLevelInAntedecent(notTerm::equals, target.getSequent());
        if(!ts.isPresent()) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        ProofRuleApplicationBuilder builder = handleControlParameters(parameters, target.getSequent());

        try {
            notTerm = new ApplTerm(BuiltinSymbols.NOT, appl.getTerm(0));
        } catch (TermBuildException e) {
            throw new RuleException("Failed to build negated term.", e);
        }

        builder.newBranch().addReplacement(selector, notTerm);
        builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);

        return builder.build();
    }

    @Override
    protected ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        Term on = parameters.getValue(ON_PARAM);
        List<TermSelector> l = RuleUtil.matchSubtermsInSequent(on::equals, target.getSequent());
        if(l.size() != 1) {
            throw new RuleException("Matching of on parameter is ambiguous");
        }
        TermSelector selector = l.get(0);

        ProofFormula formula = selector.selectTopterm(target.getSequent());
        Term term = formula.getTerm();
        if (!(term instanceof ApplTerm)) {
            throw new RuleException("Modus Tollens is only applicable on implications.");
        }
        ApplTerm appl = (ApplTerm) term;
        FunctionSymbol fs = appl.getFunctionSymbol();

        if (fs != BuiltinSymbols.IMP) {
            throw new RuleException("Modus Tollens is only applicable on implications.");
        }

        Term notTerm;
        try {
            notTerm = new ApplTerm(BuiltinSymbols.NOT, appl.getTerm(1));
        } catch (TermBuildException e) {
            throw new RuleException("Failed to build negated term.", e);
        }

        Optional<Integer> ts = RuleUtil.matchTopLevelInAntedecent(notTerm::equals, target.getSequent());
        if(!ts.isPresent()) {
            throw new RuleException("Modus Tollens is not applicable since the required TopLevel term could not be found.");
        }

        ProofRuleApplicationBuilder builder = handleControlParameters(parameters, target.getSequent());

        try {
            notTerm = new ApplTerm(BuiltinSymbols.NOT, appl.getTerm(0));
        } catch (TermBuildException e) {
            throw new RuleException("Failed to build negated term.", e);
        }

        builder.newBranch().addReplacement(selector, notTerm);
        builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);

        return builder.build();
    }
}
