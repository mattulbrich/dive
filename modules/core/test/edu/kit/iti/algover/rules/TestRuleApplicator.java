/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.impl.AndLeftRule;
import edu.kit.iti.algover.rules.impl.AndRightRule;
import edu.kit.iti.algover.rules.impl.ReplaceCutRule;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.builder.TermBuilder;
import edu.kit.iti.algover.term.builder.TreeTermTranslator;
import edu.kit.iti.algover.term.builder.TreeTermTranslatorTest;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.FormatException;
import edu.kit.iti.algover.util.ProofMockUtil;
import edu.kit.iti.algover.util.TestUtil;
import org.antlr.runtime.RecognitionException;
import org.junit.Before;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import static org.junit.Assert.assertEquals;

public class TestRuleApplicator {


    ProofRuleApplication prApp;
    SymbolTable symbTable;
    Sequent testSequent;

    Term term1;
    Term term2;
    Term term3;
    Term term4;

    @Before
    public void setup() throws RecognitionException, TermBuildException {
        setupTable();


        TermBuilder tb = new TermBuilder(symbTable);

        TreeTermTranslator ttt = new TreeTermTranslator(symbTable);

        DafnyTree t1 = TreeTermTranslatorTest.parse("b1 || b2 ==> b3");
        DafnyTree t2 = TreeTermTranslatorTest.parse("c == c2");
        DafnyTree t3 = TreeTermTranslatorTest.parse(" b1 && b2");
        DafnyTree t4 = TreeTermTranslatorTest.parse("b1 && b3");

        term1 = ttt.build(t1);
        term2 = ttt.build(t2);
        term3 = ttt.build(t3);
        term4 = ttt.build(t4);

        List<ProofFormula> antec = new ArrayList<>();
        List<ProofFormula> succ = new ArrayList<>();
        antec.add(new ProofFormula(term1));
        antec.add(new ProofFormula(term2));
        succ.add(new ProofFormula(term3));
        succ.add(new ProofFormula(term4));
        testSequent = new Sequent(antec, succ);
        //prApp = new ProofRuleApplication()
    }

    @Before
    public void setupTable() {
        Collection<FunctionSymbol> map = new ArrayList<>();
        map.add(new FunctionSymbol("i1", Sort.INT));
        map.add(new FunctionSymbol("i2", Sort.INT));
        map.add(new FunctionSymbol("i3", Sort.INT));
        map.add(new FunctionSymbol("b1", Sort.BOOL));
        map.add(new FunctionSymbol("b2", Sort.BOOL));
        map.add(new FunctionSymbol("b3", Sort.BOOL));
        map.add(new FunctionSymbol("b4", Sort.BOOL));
        map.add(new FunctionSymbol("a", Sort.get("array1")));
        map.add(new FunctionSymbol("a2", Sort.get("array2")));
        map.add(new FunctionSymbol("f", Sort.INT, Sort.INT));
        map.add(new FunctionSymbol("c", Sort.getClassSort("C")));
        map.add(new FunctionSymbol("c2", Sort.getClassSort("C")));
        symbTable = new MapSymbolTable(new BuiltinSymbols(), map);
    }

    // REVIEW: What is the assertion in this test? Only that no exception is thrown?
    @Test
    public void test() throws RuleException {
        System.out.println(testSequent);

        ProofRule pr = new AndRightRule();
        ProofNode pn = new ProofNode(null, null, null, null, testSequent, null);

        TermSelector ts = new TermSelector(TermSelector.SequentPolarity.SUCCEDENT, 1);
        Parameters params = new Parameters();
        params.putValue(AndRightRule.ON_PARAM_OPT, new TermParameter(term3, testSequent));

        //System.out.println(pr.makeApplication(pn, params));
        //RuleApplicator.applyRule(prApp, new ProofNode(null, null, null, testSequent, null));
        //RuleApplicator.changeSemisequent()

    }

    // REVIEW: What is the assertion in this test? Only that no exception is thrown?
    @Test
    public void testAddAndDelete() throws TermBuildException {
        System.out.println(testSequent.getAntecedent());
        ProofFormula f1 = new ProofFormula(term1);
        ProofFormula f2 = new ProofFormula(term2);
        ProofFormula f3 = new ProofFormula(term3);
        ProofFormula f4 = new ProofFormula(term4);
        List<ProofFormula> add = new ArrayList<>();
        add.add(f4);
        add.add(f3);

        List<ProofFormula> del = new ArrayList<>();
        del.add(f2);

        List<ProofFormula> testSemi = testSequent.getAntecedent();

        Object s = TestUtil.callStatic(RuleApplicator.class, "changeSemisequent", add, del, new ArrayList<>(), testSemi);

        System.out.println(s);
    }

    @Test
    public void applicatorTest1() throws FormatException, TermBuildException, RuleException, DafnyParserException, DafnyException {
        TermParser tp = new TermParser(symbTable);
        Sequent sequent = tp.parseSequent("i1 < i2 && i2 < i3 |- i1 < i3");

        AndLeftRule rule = new AndLeftRule();
        ProofNode pn = ProofMockUtil.mockProofNode(null, sequent.getAntecedent(), sequent.getSuccedent());
        ProofRuleApplication pra = rule.considerApplication(pn, sequent, new TermSelector("A.0"));
        List<ProofNode> newNodes = RuleApplicator.applyRule(pra, null, pn);
        assertEquals(1, newNodes.size());
        assertEquals("$lt(i1, i2), $lt(i2, i3) |- $lt(i1, i3)", newNodes.get(0).getSequent().toString());
    }

    @Test
    public void applicatorTest2() throws FormatException, TermBuildException, RuleException, DafnyParserException, DafnyException {
        TermParser tp = new TermParser(symbTable);
        Sequent sequent = tp.parseSequent("i1 < i3 |- i1 < i2 && i2 < i3");

        AndRightRule rule = new AndRightRule();
        ProofNode pn = ProofMockUtil.mockProofNode(null, sequent.getAntecedent(), sequent.getSuccedent());
        ProofRuleApplication pra = rule.considerApplication(pn, sequent, new TermSelector("S.0"));
        List<ProofNode> newNodes = RuleApplicator.applyRule(pra, null, pn);
        assertEquals(2, newNodes.size());
        assertEquals("$lt(i1, i3) |- $lt(i1, i2)", newNodes.get(0).getSequent().toString());
        assertEquals("$lt(i1, i3) |- $lt(i2, i3)", newNodes.get(1).getSequent().toString());
    }

    @Test
    public void subtypeReplacement() throws Exception {
        TermParser tp = new TermParser(symbTable);
        Proof proof = ProofMockUtil.makeProof(symbTable, "c==c");
        proof.setScriptTextAndInterpret("");
        Sequent sequent = proof.getProofRoot().getSequent();
        ReplaceCutRule rule = new ReplaceCutRule();
        Parameters p = new Parameters();
        p.checkAndPutValue(FocusProofRule.ON_PARAM_REQ, new TermParameter(new TermSelector("S.0.0"), sequent));
        p.checkAndPutValue(ReplaceCutRule.WITH_PARAM, new TermParameter(tp.parse("null"), sequent));
        ProofRuleApplication pra = rule.makeApplication(proof.getProofRoot(), p);
        List<ProofNode> newNodes = RuleApplicator.applyRule(pra, null, proof.getProofRoot());
        assertEquals(2, newNodes.size());
        assertEquals("|- $eq<C>(c, c), $eq<C>(c, null)", newNodes.get(0).getSequent().toString());
        assertEquals("|- $eq<C>(null, c)", newNodes.get(1).getSequent().toString());
    }
}
