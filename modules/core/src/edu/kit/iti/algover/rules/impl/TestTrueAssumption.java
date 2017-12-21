package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.builder.TermBuildException;

import java.util.HashMap;

public class TestTrueAssumption extends AbstractProofRule {

    public TestTrueAssumption() {
        super(new HashMap<>(), new HashMap<>());
    }

    @Override
    public String getName() {
        return "testTrueAssumption";
    }

    private ProofRuleApplication buildApplication() {
        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);
        builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);
        try {
            builder.newBranch().addAdditionAntecedent(new ProofFormula(new ApplTerm(BuiltinSymbols.TRUE)));
            builder.setTranscript("testTrueAssumption;");
        } catch (TermBuildException e) {
            e.printStackTrace();
            builder.setApplicability(ProofRuleApplication.Applicability.NOT_APPLICABLE);
        }
        return builder.build();
    }

    @Override
    public ProofRuleApplication considerApplication(ProofNode target, Sequent selection, TermSelector selector) throws RuleException {
        return buildApplication();
    }

    @Override
    public ProofRuleApplication makeApplication(ProofNode target, Parameters parameters) throws RuleException {
        return buildApplication();
    }

}
