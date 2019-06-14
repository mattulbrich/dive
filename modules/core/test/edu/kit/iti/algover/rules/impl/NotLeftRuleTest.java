/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules.impl;

import antlr.RecognitionException;
import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.rules.ProofRuleApplication.Applicability;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.builder.TreeTermTranslator;
import edu.kit.iti.algover.term.builder.TreeTermTranslatorTest;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.ProofMockUtil;
import org.junit.Before;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import static org.junit.Assert.*;

/**
 * Created by jklamroth on 1/17/18.
 */
public class NotLeftRuleTest {
    SymbolTable symbTable;
    Sequent testSequent;

    @Before
    public void setup() throws Exception {
        Collection<FunctionSymbol> map = new ArrayList<>();
        map.add(new FunctionSymbol("b1", Sort.BOOL));
        map.add(new FunctionSymbol("b2", Sort.BOOL));
        map.add(new FunctionSymbol("b3", Sort.BOOL));
        symbTable = new MapSymbolTable(new BuiltinSymbols(), map);

        TreeTermTranslator ttt = new TreeTermTranslator(symbTable);

        testSequent = TermParser.parseSequent(symbTable, "!(b1 && !b2), !b3 |- b3");
    }


    @Test
    public void basicTest() throws RuleException, TermBuildException {
        ProofRule notLeftRule = new NotLeftRule();
        ProofNode pn = ProofMockUtil.mockProofNode(null, testSequent.getAntecedent(), testSequent.getSuccedent());

        TermSelector ts = new TermSelector(TermSelector.SequentPolarity.ANTECEDENT, 0);

        ProofRuleApplication pra = notLeftRule.considerApplication(pn, testSequent, ts);
        assertEquals(Applicability.APPLICABLE, pra.getApplicability());
        List<ProofNode> newNodes = RuleApplicator.applyRule(pra, pn);
        assertEquals(1, newNodes.size());

        assertEquals("$not(b3) |- b3, $and(b1, $not(b2))", newNodes.get(0).getSequent().toString());
    }

    @Test
    public void basicTest2() throws RuleException, TermBuildException {
        ProofRule notLeftRule = new NotLeftRule();
        ProofNode pn = ProofMockUtil.mockProofNode(null, testSequent.getAntecedent(), testSequent.getSuccedent());

        TermSelector ts = new TermSelector(TermSelector.SequentPolarity.ANTECEDENT, 1);

        ProofRuleApplication pra = notLeftRule.considerApplication(pn, testSequent, ts);
        assertEquals(Applicability.APPLICABLE, pra.getApplicability());
        List<ProofNode> newNodes = RuleApplicator.applyRule(pra, pn);
        assertEquals(1, newNodes.size());

        assertEquals("$not($and(b1, $not(b2))) |- b3, ", newNodes.get(0).getSequent().toString());
    }


}
