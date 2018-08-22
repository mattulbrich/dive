package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.match.Matching;
import edu.kit.iti.algover.term.match.SequentMatcher;
import edu.kit.iti.algover.util.ImmutableList;
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
        TermSelector selector = tsForParameter.get("on");

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

        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);

        Term notTerm;
        try {
            notTerm = new ApplTerm(BuiltinSymbols.NOT, appl.getTerm(1));
        } catch (TermBuildException e) {
            throw new RuleException("Failed to build negated term.", e);
        }

        Term notTerm2;
        try {
            notTerm2 = new ApplTerm(BuiltinSymbols.NOT, appl.getTerm(0));
        } catch (TermBuildException e) {
            throw new RuleException("Failed to build negated term.", e);
        }

        builder.newBranch().addReplacement(selector, notTerm2).setLabel("mainBranch");
        builder.newBranch().addDeletionsSuccedent(target.getSequent().getSuccedent()).
                addAdditionsSuccedent(new ProofFormula(notTerm)).setLabel("assumption");
        builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);

        return builder.build();
    }

    @Override
    protected ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        TermSelector selector = tsForParameter.get("on");

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

        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);
        Term notTerm2;
        try {
            notTerm2 = new ApplTerm(BuiltinSymbols.NOT, appl.getTerm(0));
        } catch (TermBuildException e) {
            throw new RuleException("Failed to build negated term.", e);
        }

        builder.newBranch().addReplacement(selector, notTerm2).setLabel("mainBranch");
        builder.newBranch().addDeletionsSuccedent(target.getSequent().getSuccedent()).
                addAdditionsSuccedent(new ProofFormula(notTerm)).setLabel("assumption");

        return builder.build();
    }
}
