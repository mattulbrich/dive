/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;

import java.util.Collections;

public class RemoveAssumptionRule extends AbstractProofRule {

    public RemoveAssumptionRule() {
        super(ON_PARAM);
    }

    @Override
    public String getName() {
        return "removeAssumption";
    }

    @Override
    public ProofRuleApplication considerApplication(ProofNode target, Sequent selection, TermSelector selector) throws RuleException {
        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);

        if (!selector.isToplevel() || !selector.isAntecedent()) {
            builder.setApplicability(ProofRuleApplication.Applicability.NOT_APPLICABLE);
        } else {
            builder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);
            ProofFormula deleted = selector.selectTopterm(selection);
            builder.setTranscript(buildTransscript(deleted.getTerm()));
            builder.newBranch()
                    .addDeletionsAntecedent(Collections.singletonList(deleted));
        }
        return builder.build();
    }

    @Override
    public ProofRuleApplication makeApplication(ProofNode target, Parameters parameters) throws RuleException {
        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);

        checkParameters(parameters);

        Term toDelete = parameters.getValue(ON_PARAM);

        builder.newBranch()
                .addDeletionsAntecedent(Collections.singletonList(new ProofFormula(toDelete)));

        return builder.build();
    }

    private String buildTransscript(Term on) {
        return getName() + " on='" + on + "';";
    }
}
