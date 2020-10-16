/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.FocusProofRule;
import edu.kit.iti.algover.rules.NotApplicableException;
import edu.kit.iti.algover.rules.Parameters;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.ProofRuleApplicationBuilder;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermParameter;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.QuantTerm;
import edu.kit.iti.algover.term.QuantTerm.Quantifier;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.term.builder.ReplacementVisitor;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.util.Pair;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * Created by jklamroth on 10/31/18.
 */
// TODO: Make this a DefaultFocus rule like "inst". Factor out their default on
public class SkolemizationRule extends FocusProofRule {

    @Override
    public String getName() {
        return "skolemize";
    }

    @Override
    protected ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        TermParameter onParam = parameters.getValue(ON_PARAM_REQ);
        TermSelector onTs = onParam.getTermSelector();

        if(!onTs.isToplevel()) {
            throw NotApplicableException.onlyToplevel(this);
        }

        if(!(onParam.getTerm() instanceof QuantTerm)) {
            throw new NotApplicableException(getName() + " can only be applied to quantified formulas");
        }

        Quantifier expected = onTs.isAntecedent() ? Quantifier.EXISTS : Quantifier.FORALL;
        QuantTerm qTerm = (QuantTerm)onParam.getTerm();
        if (qTerm.getQuantifier() != expected) {
            throw new NotApplicableException("Only exists quantifiers in antecedent or forall quantifiers in succedent can be skolemized");
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
                    String prefix = variableTerm.getName();
                    FunctionSymbol fs = new FunctionSymbol(prefix, variableTerm.getSort());
                    int varCounter = 1;
                    while(symbolTable.getFunctionSymbol(fs.getName()) != null) {
                        fs = new FunctionSymbol(prefix + "_" + varCounter++, variableTerm.getSort());
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
