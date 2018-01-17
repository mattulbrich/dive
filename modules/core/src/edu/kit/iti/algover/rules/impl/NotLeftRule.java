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

import java.util.Collections;
import java.util.HashMap;

/**
 * Created by jklamroth on 1/11/18.
 */
public class NotLeftRule extends AbstractProofRule {

    public NotLeftRule() {
        super(createParams(), new HashMap<>());
    }

    static private HashMap<String, Class<?>> createParams() {
        HashMap<String, Class<?>> params = new HashMap<>();
        params.put("on", Term.class);
        return params;
    }

    @Override
    public String getName() {
        return "notLeft";
    }

    @Override
    public ProofRuleApplication considerApplication(ProofNode target, Sequent selection, TermSelector selector) throws RuleException {
        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);

        if(selector == null || !selector.isToplevel()) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        ProofFormula formula = selector.selectTopterm(target.getSequent());
        Term term = formula.getTerm();
        if(!(term instanceof ApplTerm)) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);
        builder.setTranscript("notLeft on='" + term + "';");

        try {
            builder.newBranch().addDeletionsAntecedent(Collections.singletonList(new ProofFormula(term)))
                    .addAdditionsSuccedent(new ProofFormula(new ApplTerm(BuiltinSymbols.NOT, term)));
        } catch(TermBuildException e){
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        return builder.build();
    }

    @Override
    public ProofRuleApplication makeApplication(ProofNode target, Parameters parameters) throws RuleException {
        Term on = parameters.getValue("on").cast(Term.class).getValue();

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
