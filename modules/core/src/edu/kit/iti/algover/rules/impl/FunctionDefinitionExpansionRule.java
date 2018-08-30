/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.dafnystructures.DafnyFunction;
import edu.kit.iti.algover.dafnystructures.DafnyFunctionSymbol;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
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
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.builder.TreeTermTranslator;
import edu.kit.iti.algover.util.ASTUtil;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.Util;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

public class FunctionDefinitionExpansionRule extends AbstractProofRule {

    public FunctionDefinitionExpansionRule() {
        super(ON_PARAM);
    }

    @Override
    public String getName() {
        return "expand";
    }

    @Override
    protected ProofRuleApplication considerApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        TermSelector selector = tsForParameter.get("on");

        // FIXME: It needs to be ensured that the selected term is not under the
        // influence of an let-update! Or that influence must be copied for the
        // justification branch.
        // Same for quantifiers

        Term term = selector.selectSubterm(target.getSequent());
        if (!(term instanceof ApplTerm)) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }
        ApplTerm appl = (ApplTerm) term;
        FunctionSymbol fs = appl.getFunctionSymbol();

        if (!(fs instanceof DafnyFunctionSymbol)) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        DafnyFunction function = ((DafnyFunctionSymbol) fs).getOrigin();

        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);
        SymbolTable symbols = target.getPVC().getSymbolTable();
        try {
            Term definition = instantiate(term, function, function.getExpression(), symbols);
            builder.newBranch().
                    addReplacement(selector, definition).
                    setLabel("continue");

            DafnyTree requires = ASTUtil.and(Util.map(function.getRequiresClauses(), DafnyTree::getLastChild));
            Term precondition = instantiate(term, function, requires, symbols);
            builder.newBranch().
                    addAdditionsSuccedent(new ProofFormula(precondition)).
                    setLabel("justify");

            builder.setApplicability(Applicability.APPLICABLE);

            return builder.build();
        } catch(TermBuildException ex) {
            throw new RuleException(ex);
        }
    }

    private Term instantiate(Term call, DafnyFunction function, DafnyTree tree, SymbolTable symbols) throws TermBuildException {
        List<Term> args = new LinkedList<>(call.getSubterms());
        List<DafnyTree> formalParams = function.getParameters();

        TreeTermTranslator ttt = new TreeTermTranslator(symbols);

        List<Pair<VariableTerm, Term>> assignments = new ArrayList<>();
        VariableTerm heapVar = new VariableTerm("heap", Sort.HEAP);
        assignments.add(new Pair(heapVar, args.remove(0)));
        ttt.bindVariable(heapVar);

        if(function.isDeclaredInClass()) {
            Term receiver = args.remove(0);
            VariableTerm recVar = new VariableTerm("this", receiver.getSort());
            assignments.add(new Pair(recVar, receiver));
            ttt.bindVariable(recVar);
        }

        assert args.size() == formalParams.size();
        for (int i = 0; i < formalParams.size(); i++) {
            Term arg = args.get(i);
            DafnyTree formalParam = formalParams.get(i);
            String name = formalParam.getFirstChildWithType(DafnyParser.ID).getText();
            VariableTerm var = new VariableTerm(name, arg.getSort());
            assignments.add(new Pair(var, arg));
            ttt.bindVariable(var);
        }

        Term translation = ttt.build(tree);

        return new LetTerm(assignments, translation);

    }

    @Override
    protected ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        return considerApplicationImpl(target, parameters);
    }
}
