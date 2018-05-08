package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.ProgramDatabase;
import edu.kit.iti.algover.dafnystructures.*;
import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.*;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.term.builder.ReplacementVisitor;
import edu.kit.iti.algover.term.match.Matching;
import edu.kit.iti.algover.term.match.TermMatcher;
import edu.kit.iti.algover.term.*;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.builder.TreeTermTranslator;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.RuleUtil;
import nonnull.NonNull;


import java.io.File;
import java.io.IOException;
import java.util.*;

/**
 * Created by jklamroth on 1/25/18.
 */
public class DafnyRule extends AbstractProofRule {
    /**
     * The dafny declaration which gave rise to this rule.
     */
    private final DafnyMethod method;


    private String name;
    private final Term searchTerm;
    private final Term replaceTerm;
    private final List<Pair<Term, String>> requiresTerms;
    private final RulePolarity polarity;

    public DafnyRule(DafnyMethod method, String name, Term st, Term rt) {
        this(method, name, st, rt, Collections.emptyList(), RulePolarity.BOTH);
    }

    public DafnyRule(DafnyMethod method, String name, Term st, Term rt, List<Pair<Term,String>> requiresTerms) {
        this(method, name, st, rt, requiresTerms, RulePolarity.BOTH);
    }

    public DafnyRule(DafnyMethod method, String name, @NonNull Term st, @NonNull Term rt, List<Pair<Term, String>> requiresTerms, RulePolarity polarity) {
        super(ON_PARAM);

        this.name = name;
        searchTerm = st;
        replaceTerm = rt;
        this.polarity = polarity;
        this.requiresTerms = requiresTerms;
        this.method = method;
    }

    @Override
    public String getName() {
        return name;
    }

    public DafnyMethod getMethod() {
        return method;
    }

    @Override
    public ProofRuleApplication considerApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        Term selected = parameters.getValue(ON_PARAM);
        List<TermSelector> l = RuleUtil.matchSubtermsInSequent(selected::equals, target.getSequent());
        if(l.size() != 1) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }

        ProofRuleApplicationBuilder proofRuleApplicationBuilder;
        try {
            Term rt;
            ImmutableList<Matching> matchings;
            if(!this.polarity.conforms(RuleUtil.getTruePolarity(l.get(0), target.getSequent()))) {
                return ProofRuleApplicationBuilder.notApplicable(this);
            } else {
                TermMatcher tm = new TermMatcher();
                matchings = tm.match(searchTerm, selected);
                if(matchings.size() == 0) {
                    return ProofRuleApplicationBuilder.notApplicable(this);
                }
                rt = matchings.get(0).instantiate(replaceTerm);
            }
            List<Pair<Term, String>> rts = new ArrayList<>();
            for(Pair<Term, String> lt : requiresTerms) {
                rts.add(new Pair<Term, String>(matchings.get(0).instantiate(lt.getFst()), lt.getSnd()));
            }
            proofRuleApplicationBuilder = new ProofRuleApplicationBuilder(this);
            proofRuleApplicationBuilder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);
            proofRuleApplicationBuilder.newBranch().addReplacement(l.get(0), rt);
            for(Pair<Term, String> lt : rts) {
                if(!RuleUtil.matchSubtermInSequent(lt.getFst()::equals, target.getSequent()).isPresent()) {
                    BranchInfoBuilder bib = proofRuleApplicationBuilder.newBranch();
                    bib.addDeletionsAntecedent(target.getSequent().getAntecedent());
                    bib.addDeletionsSuccedent(target.getSequent().getSuccedent());
                    bib.addAdditionsSuccedent(new ProofFormula(lt.getFst()));
                    bib.setLabel(lt.getSnd());
                }
            }
        } catch (TermBuildException e) {
            throw new RuleException();
        }

        return proofRuleApplicationBuilder.build();
    }

    @Override
    public ProofRuleApplication makeApplicationImpl(ProofNode target, Parameters parameters) throws RuleException {
        ProofRuleApplicationBuilder proofRuleApplicationBuilder = handleControlParameters(parameters, target.getSequent());
        try {
            Term on = parameters.getValue(ON_PARAM);

            List<TermSelector> l = RuleUtil.matchSubtermsInSequent(on::equals, target.getSequent());
            if(l.size() != 1) {
                throw new RuleException("Machting of on parameter is ambiguous");
            }
            ImmutableList<Matching> matchings;
            Term rt;
            if(!this.polarity.conforms(RuleUtil.getTruePolarity(l.get(0), target.getSequent()))) {
                throw new RuleException("Rule cant be applied to this term due to not conforming polarity.");
            } else {
                TermMatcher tm = new TermMatcher();
                matchings = tm.match(searchTerm, on);
                if(matchings.size() == 0) {
                    throw new RuleException();
                }
                rt = matchings.get(0).instantiate(replaceTerm);
            }

            proofRuleApplicationBuilder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);
            List<Pair<Term, String>> rts = new ArrayList<>();
            for(Pair<Term, String> lt : requiresTerms) {
                rts.add(new Pair<Term, String>(matchings.get(0).instantiate(lt.getFst()), lt.getSnd()));
            }

            proofRuleApplicationBuilder.newBranch().addReplacement(l.get(0), rt);

            for(Pair<Term, String> lt : rts) {
                if(!RuleUtil.matchSubtermInSequent(lt.getFst()::equals, target.getSequent()).isPresent()) {
                    BranchInfoBuilder bib = proofRuleApplicationBuilder.newBranch();
                    bib.addDeletionsAntecedent(target.getSequent().getAntecedent());
                    bib.addDeletionsSuccedent(target.getSequent().getSuccedent());
                    bib.addAdditionsSuccedent(new ProofFormula(lt.getFst()));
                    bib.setLabel(lt.getSnd());
                }
            }
        } catch (TermBuildException e) {
            throw new RuleException();
        }

        return proofRuleApplicationBuilder.build();
    }

    public enum RulePolarity {
        ANTECEDENT, SUCCEDENT, BOTH;

        public boolean conforms(TermSelector.SequentPolarity p) {
            if(p == TermSelector.SequentPolarity.ANTECEDENT && this == RulePolarity.SUCCEDENT) {
                return false;
            } else if(p == TermSelector.SequentPolarity.SUCCEDENT && this == RulePolarity.ANTECEDENT) {
                return false;
            }
            return true;
        }
    }
}