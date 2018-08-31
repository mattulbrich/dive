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
import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.QuantTerm;
import edu.kit.iti.algover.term.QuantTerm.Quantifier;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.builder.TreeTermTranslator;
import edu.kit.iti.algover.util.ASTUtil;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.Util;

import java.util.ArrayList;
import java.util.Collections;
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


            List<DafnyTree> requiresClauses = function.getRequiresClauses();
            if(!requiresClauses.isEmpty()) {
                DafnyTree requires = ASTUtil.and(Util.map(requiresClauses, DafnyTree::getLastChild));
                Term precondition = instantiate(term, function, requires, symbols);
                Term withContext = copyContext(target.getSequent(), selector, precondition);
                builder.newBranch().
                        addAdditionsSuccedent(new ProofFormula(withContext)).
                        setLabel("justify");
            }

            builder.setApplicability(Applicability.APPLICABLE);

            return builder.build();
        } catch(TermBuildException ex) {
            throw new RuleException(ex);
        }
    }

    private Term copyContext(Sequent seq, TermSelector selector, Term inner) throws RuleException {
        ProofFormula toplevel = selector.selectTopterm(seq);
        List<Term> pathList = new ArrayList<>();

        Term t = toplevel.getTerm();
        for (Integer integer : selector.getPath()) {
            pathList.add(t);
            t = t.getTerm(integer);
        }

        try {
            Collections.reverse(pathList);
            Term result = inner;
            for (Term pathTerm : pathList) {
                if (pathTerm instanceof QuantTerm) {
                    result = new QuantTerm(Quantifier.FORALL, ((QuantTerm) pathTerm).getBoundVar(), result);
                } else if (pathTerm instanceof LetTerm) {
                    result = new LetTerm(((LetTerm) pathTerm).getSubstitutions(), result);
                }
            }
            return result;
        } catch (TermBuildException ex) {
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
