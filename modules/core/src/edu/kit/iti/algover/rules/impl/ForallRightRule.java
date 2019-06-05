///*
// * This file is part of AlgoVer.
// *
// * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
// *
// */
//
//package edu.kit.iti.algover.rules.impl;
//
//import edu.kit.iti.algover.data.BuiltinSymbols;
//import edu.kit.iti.algover.proof.ProofFormula;
//import edu.kit.iti.algover.proof.ProofNode;
//import edu.kit.iti.algover.rules.AbstractProofRule;
//import edu.kit.iti.algover.rules.Parameters;
//import edu.kit.iti.algover.rules.ProofRuleApplication;
//import edu.kit.iti.algover.rules.ProofRuleApplicationBuilder;
//import edu.kit.iti.algover.rules.RuleException;
//import edu.kit.iti.algover.rules.TermParameter;
//import edu.kit.iti.algover.rules.TermSelector;
//import edu.kit.iti.algover.rules.TermSelector.SequentPolarity;
//import edu.kit.iti.algover.term.ApplTerm;
//import edu.kit.iti.algover.term.QuantTerm;
//import edu.kit.iti.algover.term.QuantTerm.Quantifier;
//import edu.kit.iti.algover.term.SchemaOccurTerm;
//import edu.kit.iti.algover.term.Sequent;
//import edu.kit.iti.algover.term.Term;
//import edu.kit.iti.algover.term.builder.TermBuildException;
//import edu.kit.iti.algover.term.builder.TermBuilder;
//import edu.kit.iti.algover.term.parser.TermParser;
//import edu.kit.iti.algover.util.RuleUtil;
//
//public class ForallRightRule extends AbstractProofRule {
//
//    @Override
//    protected ProofRuleApplication considerApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
//
//        if (!parameters.hasValue(ON_PARAM)) {
//            parameters.putValue(ON_PARAM.getName(), new TermParameter(DEFAULT_ON, target.getSequent()));
//        }
//
//        TermParameter onParam = parameters.getValue(ON_PARAM);
//
//        TermSelector onSel = onParam.getTermSelector();
//
//        if (!onSel.isToplevel() || !onSel.isSuccedent()) {
//            return ProofRuleApplicationBuilder.notApplicable(this);
//        }
//
//        Term term = onParam.getTerm();
//        if (term instanceof ApplTerm) {
//            ApplTerm applTerm = (ApplTerm) term;
//            if (applTerm.getFunctionSymbol() != BuiltinSymbols.AND) {
//                return ProofRuleApplicationBuilder.notApplicable(this);
//            }
//        }
//
//        ProofRuleApplicationBuilder prab = new ProofRuleApplicationBuilder(this);
//        prab.newBranch().addReplacement(onParam.getTermSelector(), term.getTerm(0));
//        return prab.build();
//    }
//
//    @Override
//    protected ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
//        return considerApplicationImpl(target, parameters);
//    }
//
//    @Override
//    public String getName() {
//        return "allRight";
//    }
//
//    @Override
//    public String getCategory() {
//        return "Logic";
//    }
//}
