/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
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

public class TrivialAndRight extends AbstractProofRule {

    public TrivialAndRight() {
        super(makeRequiredParameters(), makeOptionalParameters());
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
                .setTranscript("andRight on=\"" +
                        selector.selectSubterm(target.getSequent()) +  "\"");

        return builder.build();
    }

    @Override
    public ProofRuleApplication makeApplication(ProofNode target, Parameters parameters) throws RuleException {
        checkParameters(parameters);
        Parameters.TypedValue<?> onValue = parameters.getValue("on");
        //TODO what type should on have???
        // System.out.println(onValue.getType());
        Term on = onValue.cast(Term.class).getValue();
        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);

        if(!(on instanceof ApplTerm)) {
            throw new RuleException();
        }

        if(((ApplTerm)on).getFunctionSymbol() != BuiltinSymbols.AND) {
            throw new RuleException();
        }

        // this should go somewhere more central since to be used quite often.
        List<ProofFormula> succ = target.getSequent().getSuccedent();
        int no;
        for(no = 0; no < succ.size(); no++) {
            if(succ.get(no).getTerm().equals(on)) {
                break;
            }
        }

        if(no == succ.size()) {
            throw new RuleException("'on' not found");
        }

        builder.newBranch()
                .addDeletionsSuccedent(succ.get(no))
                .addAdditionsSuccedent(new ProofFormula(0, on.getTerm(0)))
                .setLabel("case 1");

        builder.newBranch()
                .addDeletionsSuccedent(succ.get(no))
                .addAdditionsSuccedent(new ProofFormula(0, on.getTerm(1)))
                .setLabel("case 2");

        return builder.build();
    }
}
