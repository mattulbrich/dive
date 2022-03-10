/*
  This file is part of DIVE.

  Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.dafnystructures.DafnyFunction;
import edu.kit.iti.algover.dafnystructures.DafnyFunctionSymbol;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.rules.ProofRuleApplication.Applicability;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.QuantTerm;
import edu.kit.iti.algover.term.QuantTerm.Quantifier;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.term.builder.AlphaNormalisation;
import edu.kit.iti.algover.term.builder.LetInlineVisitor;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.builder.TreeTermTranslator;
import edu.kit.iti.algover.util.ASTUtil;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.RuleUtil;
import edu.kit.iti.algover.util.Util;

import java.util.*;
import java.util.stream.Collectors;

/**
 * This proof rule allows one to expand an application of a function symbol to
 * its definition.
 *
 * <h2>Parameters</h2>
 *
 * Currently, only the on-parameter is supported. In the future, (for exhaustive
 * etc.) applications, parameters like "functions" are planned to restrict the
 * reach of the formula.
 *
 * @author mulbrich
 */
public class FunctionDefinitionExpansionRule extends FocusProofRule {

    static ParameterDescription<Boolean> INLINE_PARAM =
            new ParameterDescription<>("inlineLet", ParameterType.BOOLEAN, false, true);

    public FunctionDefinitionExpansionRule () {
        super(ON_PARAM_REQ, INLINE_PARAM);
    }
    @Override
    public String getName() {
        return "expand";
    }

    @Override
    protected ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        TermParameter onParam = parameters.getValue(ON_PARAM_REQ);
        TermSelector selector;
        if(onParam == null) {
            selector = inferOnParam(target.getSequent());
            if(selector == null) {
                throw NotApplicableException.requiresParameter(this, ON_PARAM_REQ);
            }
        } else {
            selector = parameters.getValue(ON_PARAM_REQ).getTermSelector();
        }
        Boolean inline = parameters.getValue(INLINE_PARAM);

        Term term = selector.selectSubterm(target.getSequent());

        if (!(term instanceof ApplTerm)) {
            throw NotApplicableException.onlyOperator(this, "Dafny function");
        }
        ApplTerm appl = (ApplTerm) term;
        FunctionSymbol fs = appl.getFunctionSymbol();

        if (!(fs instanceof DafnyFunctionSymbol)) {
            throw NotApplicableException.onlyOperator(this, "Dafny function");
        }

        DafnyFunction function = ((DafnyFunctionSymbol) fs).getOrigin();

        ProofRuleApplicationBuilder builder = new ProofRuleApplicationBuilder(this);
        SymbolTable symbols = target.getAllSymbols();
        try {
            Term definition = instantiate(term, function, function.getExpression(), symbols, inline);
            Term alphaNormalisedDef = AlphaNormalisation.normalise(definition);
            builder.newBranch().
                    addReplacement(selector, alphaNormalisedDef).
                    setLabel("continue");


            List<DafnyTree> requiresClauses = function.getRequiresClauses();
            if(!requiresClauses.isEmpty()) {
                DafnyTree requires = ASTUtil.and(Util.map(requiresClauses, DafnyTree::getLastChild));
                Term precondition = instantiate(term, function, requires, symbols, inline);
                Term withContext = copyContext(target.getSequent(), selector, precondition);
                Term alphaNormalised = AlphaNormalisation.normalise(withContext);
                builder.newBranch().
                        addAdditionsSuccedent(new ProofFormula(alphaNormalised)).
                        setLabel("justify");
            }

            builder.setApplicability(Applicability.APPLICABLE);

            return builder.build();
        } catch(TermBuildException ex) {
            throw new RuleException(ex);
        }
    }

    private Term inferOnParam(Term term) {
        for(Term t : term.getSubterms()) {

            if (!(t instanceof ApplTerm) || !(((ApplTerm) t).getFunctionSymbol() instanceof DafnyFunctionSymbol)) {
                Term ts = inferOnParam(t);
                if(ts != null) return ts;
                continue;
            }
            return t;
        }
        return null;
    }

    private TermSelector inferOnParam(Sequent s) {
        for(ProofFormula pf : s.getAntecedent()) {
            Term term = pf.getTerm();

            if (!(term instanceof ApplTerm) || !(((ApplTerm) term).getFunctionSymbol() instanceof DafnyFunctionSymbol)) {
                Term ts = inferOnParam(term);
                if(ts != null) {
                    Optional<TermSelector> ots = RuleUtil.matchSubtermInSequent(ts::equals, s);
                    if(ots.isPresent()) {
                        return ots.get();
                    } else {
                        //This should never happen
                        continue;
                    }
                }
                continue;
            }
            return new TermSelector(TermSelector.SequentPolarity.ANTECEDENT, s.getAntecedent().indexOf(pf));
        }
        for(ProofFormula pf : s.getSuccedent()) {
            Term term = pf.getTerm();

            if (!(term instanceof ApplTerm) || !(((ApplTerm) term).getFunctionSymbol() instanceof DafnyFunctionSymbol)) {
                Term ts = inferOnParam(term);
                if(ts != null) {
                    Optional<TermSelector> ots = RuleUtil.matchSubtermInSequent(ts::equals, s);
                    if(ots.isPresent()) {
                        return ots.get();
                    } else {
                        //This should never happen
                        continue;
                    }
                }
                continue;
            }
            return new TermSelector(TermSelector.SequentPolarity.SUCCEDENT, s.getAntecedent().indexOf(pf));
        }
        return null;
    }

    /*
     * Embed the term inner into the variable-binding context that the given
     * term selector possesses.
     *
     * All let-bindings are copied and all quantifiers become universal
     * quantifications.
     */
    private static Term copyContext(Sequent seq, TermSelector selector, Term inner) throws RuleException {
        ProofFormula toplevel = selector.selectTopterm(seq);
        List<Term> pathList = new ArrayList<>();

        Term t = toplevel.getTerm();
        for (int elem : selector.getPath()) {
            pathList.add(t);
            t = t.getTerm(elem);
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

    /**
     * Instantiate the free parameters in a formula by the arguments provided to
     * a function call.
     *
     * @param call     the term capturing the call in logic
     * @param function the called function
     * @param tree     the formula which is to be instantiated
     * @param symbols  table to look up function symbols during translation
     * @return a freshly created term
     * @throws TermBuildException if the term cannot be instantiated. The
     *                            parsing and type resolution facilities should
     *                            prevent these exceptions.
     */
    private static Term instantiate(Term call, DafnyFunction function, DafnyTree tree, SymbolTable symbols, Boolean inline) throws TermBuildException {
        List<Term> args = new LinkedList<>(call.getSubterms());
        List<DafnyTree> formalParams = function.getParameters();

        TreeTermTranslator ttt = new TreeTermTranslator(symbols);

        List<Pair<VariableTerm, Term>> assignments = new ArrayList<>();
        VariableTerm heapVar = new VariableTerm("heap", Sort.HEAP);
        assignments.add(new Pair<>(heapVar, args.remove(0)));
        ttt.bindVariable(heapVar);

        if(function.isDeclaredInClass()) {
            Term receiver = args.remove(0);
            VariableTerm recVar = new VariableTerm("this", receiver.getSort());
            assignments.add(new Pair<>(recVar, receiver));
            ttt.bindVariable(recVar);
        }

        assert args.size() == formalParams.size();
        for (int i = 0; i < formalParams.size(); i++) {
            Term arg = args.get(i);
            DafnyTree formalParam = formalParams.get(i);
            String name = formalParam.getFirstChildWithType(DafnyParser.ID).getText();
            VariableTerm var = new VariableTerm(name, arg.getSort());
            assignments.add(new Pair<>(var, arg));
            ttt.bindVariable(var);
        }

        Term translation = ttt.build(tree);
        LetTerm letTranslation = new LetTerm(assignments, translation);
        /**
         * Use {@link SubstitutionVisitor} that introduces bugfix for heap updates.
         */
        if(inline) {
            Map<String, Term> substitutionMap =
                    letTranslation.getSubstitutions()
                            .stream()
                            .collect(Collectors.toMap(pair -> pair.fst.getName(), pair -> pair.snd));

            Term inner = letTranslation.getTerm(0);
            try {
                Term result = inner.accept(new SubstitutionVisitor(), substitutionMap);
                result = AlphaNormalisation.normalise(result);

                return result;
            }
            catch(RuleException re) {
                re.printStackTrace();
            }
        }

        return letTranslation;

    }

}
