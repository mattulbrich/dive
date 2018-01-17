package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.RuleUtil;

import java.util.Collections;
import java.util.HashMap;
import java.util.Optional;

/**
 * Created by jklamroth on 1/17/18.
 */
public class OrLeftRule extends AbstractProofRule {

    public OrLeftRule() {
        super(createParams(), new HashMap<>());
    }

    private static HashMap createParams() {
        HashMap<String, Class<?>> params = new HashMap<>();
        params.put("on", Term.class);
        return params;
    }

    @Override
    public String getName() {
        return "orLeft";
    }

    @Override
    public ProofRuleApplication considerApplication(ProofNode target, Sequent selection, TermSelector selector) throws RuleException {
        if(selector == null || !selector.isToplevel() || selector.isSuccedent()) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }
        ProofFormula f = selector.selectTopterm(target.getSequent());
        Term t = f.getTerm();

        if(!(t instanceof ApplTerm)) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }
        ApplTerm at = (ApplTerm)t;
        if(at.getFunctionSymbol() != BuiltinSymbols.OR) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);
        builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);
        builder.setTranscript("orLeft on='" + at + "';");

        builder.newBranch().addDeletionsAntecedent(Collections.singletonList(new ProofFormula(at))).
                addAdditionAntecedent(new ProofFormula(at.getTerm(0)));
        builder.newBranch().addDeletionsAntecedent(Collections.singletonList(new ProofFormula(at))).
                addAdditionAntecedent(new ProofFormula(at.getTerm(1)));

        return builder.build();
    }

    @Override
    public ProofRuleApplication makeApplication(ProofNode target, Parameters parameters) throws RuleException {
        Term p = parameters.getValue("on").cast(Term.class).getValue();
        if(!(p instanceof ApplTerm)) {
            throw new RuleException("orLeft has to be applied to an ApplicationTerm");
        }
        ApplTerm on = (ApplTerm)p;
        if(on.getFunctionSymbol() != BuiltinSymbols.OR) {
            throw new RuleException("orLeft has to be applied to a term with function symbol \"||\"");
        }
        if(Optional.empty().equals(RuleUtil.matchTopLevelInAntedecent(on::equals, target.getSequent()))) {
            throw new RuleException("orLeft can only be applied to a term in the antecedent");
        }


        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);
        builder.newBranch().addDeletionsAntecedent(Collections.singletonList(new ProofFormula(on))).
                addAdditionAntecedent(new ProofFormula(on.getTerm(0)));
        builder.newBranch().addDeletionsAntecedent(Collections.singletonList(new ProofFormula(on))).
                addAdditionAntecedent(new ProofFormula(on.getTerm(1)));

        return builder.build();
    }
}
