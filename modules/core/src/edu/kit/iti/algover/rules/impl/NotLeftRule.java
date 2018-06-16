package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.script.callhandling.BuiltinCommands;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.util.RuleUtil;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;

/**
 * Created by jklamroth on 1/11/18.
 */
public class NotLeftRule extends AbstractProofRule {

    public NotLeftRule() {
        super(ON_PARAM);
    }

    @Override
    public String getName() {
        return "notLeft";
    }

    @Override
    public ProofRuleApplication considerApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);

        Term on = parameters.getValue(ON_PARAM);
        List<TermSelector> l = RuleUtil.matchSubtermsInSequent(on::equals, target.getSequent());
        if(l.size() != 1) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        if(l.get(0) == null || !l.get(0).isToplevel()) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        ProofFormula formula = l.get(0).selectTopterm(target.getSequent());
        Term term = formula.getTerm();
        if(!(term instanceof ApplTerm)) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);

        try {
            builder.newBranch().addDeletionsAntecedent(Collections.singletonList(new ProofFormula(term)))
                    .addAdditionsSuccedent(new ProofFormula(new ApplTerm(BuiltinSymbols.NOT, term)));
        } catch(TermBuildException e){
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        return builder.build();
    }

    @Override
    public ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        Term on = parameters.getValue(ON_PARAM);

        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);
        try {
            builder.newBranch().addDeletionsAntecedent(Collections.singletonList(new ProofFormula(on)))
                    .addAdditionsSuccedent(new ProofFormula(new ApplTerm(BuiltinSymbols.NOT, on)));
        } catch (TermBuildException e) {
            throw new RuleException();
        }

        return builder.build();
    }
}
