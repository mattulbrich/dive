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


import java.io.File;
import java.io.IOException;
import java.util.*;

/**
 * Created by jklamroth on 1/25/18.
 */
public class DafnyRule extends AbstractProofRule {
    private String name;
    private String fileName;
    private SymbolTable symbolTable;
    private List<String> programVars;
    private DafnyTree tree;
    private final Term searchTerm;
    private final Term replaceTerm;

    public DafnyRule(String name, Term st, Term rt) {
        super(ON_PARAM);

        this.name = name;
        searchTerm = st;
        replaceTerm = rt;
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public ProofRuleApplication considerApplication(ProofNode target, Sequent selection, TermSelector selector) throws RuleException {
        Term selected = selector.selectTopterm(target.getSequent()).getTerm();
        TermMatcher tm = new TermMatcher();
        ImmutableList<Matching> matchings = tm.match(searchTerm, selected);
        if(matchings.size() == 0) {
            return ProofRuleApplicationBuilder.notApplicable(this);
        }
        ProofRuleApplicationBuilder proofRuleApplicationBuilder;
        try {
            Term rt = matchings.get(0).instantiate(replaceTerm);
            proofRuleApplicationBuilder = new ProofRuleApplicationBuilder(this);
            proofRuleApplicationBuilder.setApplicability(ProofRuleApplication.Applicability.APPLICABLE);
            proofRuleApplicationBuilder.setTranscript(getTranscript(new Pair<>("on", selected)));
            proofRuleApplicationBuilder.newBranch().addReplacement(selector, rt);
        } catch (TermBuildException e) {
            throw new RuleException();
        }

        return proofRuleApplicationBuilder.build();
    }

    @Override
    public ProofRuleApplication makeApplication(ProofNode target, Parameters parameters) throws RuleException {
        Term on = parameters.getValue(ON_PARAM);

        TermMatcher tm = new TermMatcher();
        ImmutableList<Matching> matchings = tm.match(searchTerm, on);
        if(matchings.size() == 0) {
            throw new RuleException();
        }

        ProofRuleApplicationBuilder proofRuleApplicationBuilder;
        try {
            Term rt = matchings.get(0).instantiate(replaceTerm);
            proofRuleApplicationBuilder = new ProofRuleApplicationBuilder(this);
            if(Optional.empty().equals(RuleUtil.matchTopLevelInAntedecent(on::equals, target.getSequent()))) {
                proofRuleApplicationBuilder.newBranch().addDeletionsSuccedent(new ProofFormula(on)).
                        addAdditionsSuccedent(new ProofFormula(rt));
            } else {
                proofRuleApplicationBuilder.newBranch().addDeletionsAntecedent(Collections.singletonList(new ProofFormula(on))).
                        addAdditionAntecedent(new ProofFormula(rt));
            }
        } catch (TermBuildException e) {
            throw new RuleException();
        }

        return proofRuleApplicationBuilder.build();
    }
}