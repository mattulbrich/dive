/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules.impl;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.AbstractProofRule;
import edu.kit.iti.algover.rules.Parameters;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.ProofRuleApplication.Applicability;
import edu.kit.iti.algover.rules.ProofRuleApplicationBuilder;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.util.RuleUtil;

public class TrivialAndRight extends AbstractProofRule {

    public TrivialAndRight() {
        super(ON_PARAM);
    }

    private static Map<String, Class<?>> makeOptionalParameters() {
        Map<String, Class<?>> result = new HashMap<>();
        result.put("deep", Boolean.class);
        return result;
    }

    private static Map<String, Class<?>> makeRequiredParameters() {
        Map<String, Class<?>> result = new HashMap<>();
        result.put("on", Term.class);
        return result;
    }

    @Override
    public String getName() {
        return "andRight";
    }

    @Override
    public ProofRuleApplication considerApplication(ProofNode target, Sequent selection,
                                                    TermSelector selector)
            throws RuleException {

        if (selector != null && !selector.isToplevel()) {
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

        builder.newBranch().addReplacement(selector, appl.getTerm(0));
        builder.newBranch().addReplacement(selector, appl.getTerm(1));
        builder.setApplicability(Applicability.APPLICABLE)
                .setTranscript("andRight on='" +
                        selector.selectSubterm(target.getSequent()) +  "';\n");

        return builder.build();
    }

    @Override
    public ProofRuleApplication makeApplication(ProofNode target, Parameters parameters) throws RuleException {
        checkParameters(parameters);
        Term on = parameters.getValue(ON_PARAM);
        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);

        if(!(on instanceof ApplTerm)) {
            throw new RuleException();
        }

        if(((ApplTerm)on).getFunctionSymbol() != BuiltinSymbols.AND) {
            throw new RuleException();
        }

        int no = RuleUtil.matchTopLevelInSuccedent(on::equals, target.getSequent())
                .orElseThrow(() -> new RuleException("'on' not found"));

        builder.newBranch()
                .addDeletionsSuccedent(target.getSequent().getSuccedent().get(no))
                .addAdditionsSuccedent(new ProofFormula(on.getTerm(0)))
                .setLabel("case 1");

        builder.newBranch()
                .addDeletionsSuccedent(target.getSequent().getSuccedent().get(no))
                .addAdditionsSuccedent(new ProofFormula(on.getTerm(1)))
                .setLabel("case 2");

        return builder.build();
    }
}
