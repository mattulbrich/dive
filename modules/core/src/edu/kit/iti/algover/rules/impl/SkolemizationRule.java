/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.AbstractProofRule;
import edu.kit.iti.algover.rules.Parameters;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.ProofRuleApplicationBuilder;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermParameter;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.QuantTerm;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.term.builder.ReplacementVisitor;
import edu.kit.iti.algover.term.builder.TermBuildException;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Created by jklamroth on 10/31/18.
 */
public class SkolemizationRule extends AbstractProofRule {

    public SkolemizationRule() {
        super(ON_PARAM);
    }

    @Override
    public String getName() {
        return "skolemize";
    }

    @Override
    public ProofRuleApplication considerApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        TermParameter onParam = parameters.getValue(ON_PARAM);
        if(onParam == null) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        TermSelector onTs = onParam.getTermSelector();
        if(!onTs.isToplevel()) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        if(!(onParam.getTerm() instanceof QuantTerm)) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        QuantTerm qTerm = (QuantTerm)onParam.getTerm();
        if(qTerm.getQuantifier() != QuantTerm.Quantifier.EXISTS) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        Term rt;
        SymbolTable syms = target.getAllSymbols();
        SkolemizationVisitor sv = new SkolemizationVisitor(syms);
        try {
            rt = onParam.getTerm().accept(sv, new HashMap<VariableTerm, ApplTerm>());
        } catch(TermBuildException e) {
            throw new RuleException("Error trying to skolemize term " + onParam.getTerm(), e);
        }

        ProofRuleApplicationBuilder prab = new ProofRuleApplicationBuilder(this);
        prab.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);
        prab.setNewFuctionSymbols(sv.getNewFunctionSymbols());
        if(rt != null) {
            prab.newBranch().addReplacement(onTs, rt);
        }
        return prab.build();
    }

    @Override
    protected ProofRuleApplication makeApplicationImpl_OLD(ProofNode target, Parameters parameters) throws RuleException {
        TermParameter onParam = parameters.getValue(ON_PARAM);
        if(onParam == null) {
            throw new RuleException();
        }

        TermSelector onTs = onParam.getTermSelector();
        if(!onTs.isToplevel()) {
            throw new RuleException();
        }

        if(!(onParam.getTerm() instanceof QuantTerm)) {
            throw new RuleException();
        }

        QuantTerm qTerm = (QuantTerm)onParam.getTerm();
        if(qTerm.getQuantifier() != QuantTerm.Quantifier.EXISTS) {
            throw new RuleException();
        }

        Term rt;
        SymbolTable syms = target.getAllSymbols();
        SkolemizationVisitor sv = new SkolemizationVisitor(syms);
        try {
            rt = onParam.getTerm().accept(sv, new HashMap<VariableTerm, ApplTerm>());
        } catch(TermBuildException e) {
            throw new RuleException("Error trying to skolemize term " + onParam.getTerm(), e);
        }

        ProofRuleApplicationBuilder prab = new ProofRuleApplicationBuilder(this);
        prab.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);
        prab.setNewFuctionSymbols(sv.getNewFunctionSymbols());
        if(rt != null) {
            prab.newBranch().addReplacement(onTs, rt);
        }
        return prab.build();
    }

    private class SkolemizationVisitor extends ReplacementVisitor<Map<VariableTerm, ApplTerm>> {
        private int varCounter = 0;
        private final SymbolTable symbolTable;
        private List<FunctionSymbol> newFs;

        public SkolemizationVisitor(SymbolTable symbolTable) {
            this.symbolTable = symbolTable;
            newFs = new ArrayList<>();
        }

        @Override
        public Term visit(QuantTerm quantTerm, Map<VariableTerm, ApplTerm> arg) throws TermBuildException {
            arg.put(quantTerm.getBoundVar(), null);
            return super.visit(quantTerm, arg).getTerm(0);
        }

        @Override
        public Term visit(VariableTerm variableTerm, Map<VariableTerm, ApplTerm> arg) throws TermBuildException {
            if(arg.keySet().contains(variableTerm)) {
                if(arg.get(variableTerm) != null) {
                    return arg.get(variableTerm);
                } else {
                    FunctionSymbol fs = new FunctionSymbol("skvar" + varCounter++, variableTerm.getSort());
                    while(symbolTable.getFunctionSymbol(fs.getName()) != null) {
                        fs = new FunctionSymbol("skvar" + varCounter++, variableTerm.getSort());
                    }
                    newFs.add(fs);
                    ApplTerm at = new ApplTerm(fs);
                    arg.put(variableTerm, at);
                    return at;
                }
            }
            return super.visit(variableTerm, arg);
        }

        public List<FunctionSymbol> getNewFunctionSymbols() {
            return newFs;
        }
    }
}
