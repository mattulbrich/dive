package edu.kit.iti.algover.rules.impl;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.AbstractProofRule;
import edu.kit.iti.algover.rules.Parameters;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.ProofRuleApplication.Applicability;
import edu.kit.iti.algover.rules.ProofRuleApplicationBuilder;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.rules.TermSelector.SequentPolarity;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;

// ALPHA ... Just for demo purposes so far.

public class PropositionalExpansionRule extends AbstractProofRule {

    public PropositionalExpansionRule() {
        super(makeRequiredParameters(), makeOptionalParameters());
    }

    private static Map<String, Class<?>> makeRequiredParameters() {
        Map<String, Class<?>> result = new HashMap<>();
        result.put("on", Term.class);
        return result;
    }

    private static Map<String, Class<?>> makeOptionalParameters() {
        Map<String, Class<?>> result = new HashMap<>();
        result.put("deep", Boolean.class);
        return result;
    }

    @Override
    public String getName() {
        return "prop-expand";
    }

    @Override
    public ProofRuleApplication considerApplication(ProofNode target, Sequent selection,
                                                    TermSelector selector)
            throws RuleException {

        if (selector != null) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        if (selection == null) {
            selection = target.getSequent();
        }

        boolean allowSplit = true;

        PropositionalExpander pex = new PropositionalExpander();
        List<ProofFormula> deletionsAnte = new ArrayList<ProofFormula>();
        List<ProofFormula> deletionsSucc = new ArrayList<ProofFormula>();

        for (ProofFormula formula : selection.getAntecedent()) {
            if (pex.expand(formula, SequentPolarity.ANTECEDENT, allowSplit)) {
                deletionsAnte.add(formula);
            }
        }

        for (ProofFormula formula : selection.getSuccedent()) {
            if (pex.expand(formula, SequentPolarity.SUCCEDENT, allowSplit)) {
                deletionsSucc.add(formula);
            }
        }

        List<Sequent> sequents = pex.getSequents();

        if (deletionsAnte.isEmpty() && deletionsSucc.isEmpty()) {
            // nothing to be done
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);

        for (Sequent sequent : sequents) {
            builder.newBranch().addAdditions(sequent)
                    .addDeletionsAntecedent(deletionsAnte)
                    .addDeletionsSuccedent(deletionsSucc);
        }

        builder.setApplicability(Applicability.APPLICABLE)
                .setTranscript("todo");

        return builder.build();
    }

    @Override
    public ProofRuleApplication makeApplication(ProofNode target, Parameters parameters) throws RuleException {
        checkParameters(parameters);

        throw new Error("not finished yet");
    }

}
