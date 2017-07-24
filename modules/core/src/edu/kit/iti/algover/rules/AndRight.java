/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import edu.kit.iti.algover.script.ScriptTree;
import edu.kit.iti.algover.term.Sequent;

/**
 * Created by sarah on 11/2/15.
 */
public class AndRight extends AbstractProofRule<AndRight.Parameters> {

    public class Parameters {
        @Parameter("deep") boolean deep;
    }

    @Override
    public String getName() {
        return "andRight";
    }

    @Override
    public ProofRuleApplication<Parameters> consider(Parameters params,
            Sequent sequent, Sequent selection, TermSelector selector) throws RuleException {

        if(selector != null && !selector.isToplevel()) {
            notApplicable();
        }

        try {
            if(selection.isEmpty()) {
                selection = selector.selectSequent(sequent);
            }
        } catch (Exception e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

        // ...

        return null;
    }



    @Override
    public Parameters parseArguments(ScriptTree tree) {
        // TODO Auto-generated method stub
        return null;
    }
}
