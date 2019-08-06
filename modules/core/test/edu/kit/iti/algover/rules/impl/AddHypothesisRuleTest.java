/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.ProofMockUtil;
import org.junit.Before;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import static org.junit.Assert.assertEquals;

/**
 * Created by jklamroth on 5/16/18.
 */
public class AddHypothesisRuleTest {
    SymbolTable symbTable;
    Sequent testSequent;

    @Before
    public void setup() throws TermBuildException, org.antlr.runtime.RecognitionException {
        Collection<FunctionSymbol> map = new ArrayList<>();
        map.add(new FunctionSymbol("b1", Sort.BOOL));
        map.add(new FunctionSymbol("b2", Sort.BOOL));
        map.add(new FunctionSymbol("b3", Sort.BOOL));
        symbTable = new MapSymbolTable(new BuiltinSymbols(), map);
    }

    @Test
    public void basicApplicationTest() throws DafnyParserException, DafnyException, TermBuildException, RuleException {
        TermParser tp = new TermParser(symbTable);
        String sequentString = "b1 || b2, b3 |- b3 && b2 || b3 && b1";
        Sequent s = tp.parseSequent(sequentString);
        ProofNode pn = ProofMockUtil.mockProofNode(null, s.getAntecedent(), s.getSuccedent());
        AddHypothesisRule rule = new AddHypothesisRule();
        Parameters params = new Parameters();
        params.putValue(AddHypothesisRule.WITH_PARAM, new TermParameter(tp.parse("b1"), s));
        ProofRuleApplication pra = rule.makeApplication(pn,  params);
        List<ProofNode> newNodes = RuleApplicator.applyRule(pra, pn);

        assertEquals(2, newNodes.size());
        assertEquals(newNodes.get(0).getSequent().toString(), "$or(b1, b2), b3, b1 |- $or($and(b3, b2), $and(b3, b1))");
        assertEquals(newNodes.get(1).getSequent().toString(), "$or(b1, b2), b3 |- $or($and(b3, b2), $and(b3, b1)), b1");
    }
}
