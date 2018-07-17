/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.impl.LetSubstitutionRule;
import edu.kit.iti.algover.rules.impl.OrLeftRule;
import edu.kit.iti.algover.rules.impl.TrivialAndRight;
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

        ProofRule pr = new TrivialAndRight();
        ProofNode pn = new ProofNode(null, null, testSequent, null);

        TermSelector ts = new TermSelector(TermSelector.SequentPolarity.SUCCEDENT, 1);
        Parameters params = new Parameters();
        params.putValue("on", term3);

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

        System.out.println(RuleApplicator.changeSemisequent(add, del, new ArrayList<>(), testSemi));
    }

    @Test
    public void testExhaustiveApplication() throws DafnyException, DafnyParserException, TermBuildException, FormatException, RuleException {
        TermParser tp = new TermParser(symbTable);
        Sequent seq = tp.parseSequent("(let b1 := b2 :: b1) |- b2");

        ProofRule letSub = new LetSubstitutionRule();
        ProofNode pn = ProofMockUtil.mockProofNode(null, seq.getAntecedent(), seq.getSuccedent());
        ProofRuleApplication pra = letSub.considerApplication(pn, seq, new TermSelector("A.0"));
        List<ProofNode> proofNodes = RuleApplicator.applyRuleExhaustive(letSub, pn, new TermSelector("A.0"));
        assertEquals(1, proofNodes.size());
        assertEquals("[b2] ==> [b2]", proofNodes.get(0).getSequent().toString());

        seq = tp.parseSequent("let b3 := true :: let b2 := false :: b3 || b2 |- b2");

        letSub = new LetSubstitutionRule();
        pn = ProofMockUtil.mockProofNode(null, seq.getAntecedent(), seq.getSuccedent());
        pra = letSub.considerApplication(pn, seq, new TermSelector("A.0"));
        proofNodes = RuleApplicator.applyRuleExhaustive(letSub, pn, new TermSelector("A.0"));
        assertEquals(1, proofNodes.size());
        assertEquals("[$or(true, false)] ==> [b2]", proofNodes.get(0).getSequent().toString());

        seq = tp.parseSequent("b1 || (b2 || b3), b4 |- b2");

        letSub = new OrLeftRule();
        pn = ProofMockUtil.mockProofNode(null, seq.getAntecedent(), seq.getSuccedent());
        pra = letSub.considerApplication(pn, seq, new TermSelector("A.0"));
        proofNodes = RuleApplicator.applyRuleExhaustive(letSub, pn, new TermSelector("A.0"));

        assertEquals(3, proofNodes.size());
        assertEquals("[b1, b4] ==> [b2]", proofNodes.get(0).getSequent().toString());
        assertEquals("[b2, b4] ==> [b2]", proofNodes.get(1).getSequent().toString());
        assertEquals("[b3, b4] ==> [b2]", proofNodes.get(2).getSequent().toString());

        seq = tp.parseSequent("b1 && (b2 || b3), b2 |- b2");

        letSub = new OrLeftRule();
        pn = ProofMockUtil.mockProofNode(null, seq.getAntecedent(), seq.getSuccedent());
        pra = letSub.considerApplication(pn, seq, new TermSelector("A.0"));
        proofNodes = RuleApplicator.applyRuleExhaustive(letSub, pn, new TermSelector("A.0"));
        assertEquals(1, proofNodes.size());
        assertEquals("[$and(b1, $or(b2, b3)), b2] ==> [b2]", proofNodes.get(0).getSequent().toString());

        seq = tp.parseSequent("b1 || (b2 && b3), b2 |- b2");

        letSub = new OrLeftRule();
        pn = ProofMockUtil.mockProofNode(null, seq.getAntecedent(), seq.getSuccedent());
        pra = letSub.considerApplication(pn, seq, new TermSelector("A.0"));
        proofNodes = RuleApplicator.applyRuleExhaustive(letSub, pn, new TermSelector("A.0"));
        assertEquals(2, proofNodes.size());
        assertEquals("[b1, b2] ==> [b2]", proofNodes.get(0).getSequent().toString());
        assertEquals("[$and(b2, b3), b2] ==> [b2]", proofNodes.get(1).getSequent().toString());

        seq = tp.parseSequent("i1 + 0 + 1 + 0 |- b2");

        try {
            letSub = DafnyRuleUtil.generateDafnyRuleFromFile("./modules/core/test-res/edu/kit/iti/algover/dafnyrules/addzero.dfy");
        } catch (DafnyRuleException e) {
            System.out.println("Exception corrued during laoding dafny rule addzero2.dfy.");
            e.printStackTrace();
        }
        pn = ProofMockUtil.mockProofNode(null, seq.getAntecedent(), seq.getSuccedent());
        pra = letSub.considerApplication(pn, seq, new TermSelector("A.0"));
        proofNodes = RuleApplicator.applyRuleExhaustive(letSub, pn, new TermSelector("A.0"));
        assertEquals(1, proofNodes.size());
        assertEquals("[$plus($plus(i1, 0), 1)] ==> [b2]", proofNodes.get(0).getSequent().toString());

        seq = tp.parseSequent("i1 + 0 + 1 + 0 |- b2");

        try {
            letSub = DafnyRuleUtil.generateDafnyRuleFromFile("./modules/core/test-res/edu/kit/iti/algover/dafnyrules/addzero2.dfy");
        } catch (DafnyRuleException e) {
            System.out.println("Exception corrued during laoding dafny rule addzero2.dfy.");
            e.printStackTrace();
        }
        pn = ProofMockUtil.mockProofNode(null, seq.getAntecedent(), seq.getSuccedent());
        pra = letSub.considerApplication(pn, seq, new TermSelector("A.0"));
        proofNodes = RuleApplicator.applyRuleExhaustive(letSub, pn, new TermSelector("A.0"));
        assertEquals(4, proofNodes.size());
        assertEquals("[] ==> [$eq<int>(0, 0)]", proofNodes.get(0).getSequent().toString());
        assertEquals("[] ==> [$eq<int>(1, 0)]", proofNodes.get(1).getSequent().toString());
        assertEquals("[i1] ==> [b2]", proofNodes.get(2).getSequent().toString());
        assertEquals("[] ==> [$eq<int>(0, 0)]", proofNodes.get(3).getSequent().toString());

    }

    @Test
    public void testDeepExhaustiveApplication() throws DafnyException, DafnyParserException, TermBuildException, FormatException, RuleException {
        TermParser tp = new TermParser(symbTable);
        Sequent seq;

        ProofRule letSub = null;
        ProofNode pn;

        seq = tp.parseSequent("i1 + 0 + 1 + 0, i3 + 0 |- b2");

        try {
            letSub = DafnyRuleUtil.generateDafnyRuleFromFile("./modules/core/test-res/edu/kit/iti/algover/dafnyrules/addzero.dfy");
        } catch (DafnyRuleException e) {
            System.out.println("Exception corrued during laoding dafny rule addzero2.dfy.");
            e.printStackTrace();
        }
        pn = ProofMockUtil.mockProofNode(null, seq.getAntecedent(), seq.getSuccedent());
        List<ProofNode> proofNodes = RuleApplicator.applyRuleDeepExhaustive(letSub, pn, new TermSelector("A.0"));
        proofNodes.forEach(node -> {
            System.out.println("node = " + node);
        });
        assertEquals(1, proofNodes.size());
        assertEquals("[$plus(i1, 1), $plus(i3, 0)] ==> [b2]", proofNodes.get(0).getSequent().toString());
    }

    @Test
    public void testDifferentTypeApplication() throws DafnyException, DafnyParserException, TermBuildException, FormatException, RuleException {
        TermParser tp = new TermParser(symbTable);

        Sequent seq = tp.parseSequent("let b3 := true :: let b2 := false :: b3 || b2 |- b2");

        ProofRule letSub = new LetSubstitutionRule();
        ProofNode pn = ProofMockUtil.mockProofNode(null, seq.getAntecedent(), seq.getSuccedent());
        Parameters parameters = new Parameters();
        parameters.putValue("on", new TermSelector("A.0").selectSubterm(seq));
        parameters.putValue("type", "once");
        ProofRuleApplication pra = letSub.makeApplication(pn, parameters);
        List<ProofNode> proofNodes = RuleApplicator.applyRule(pra, pn);
        assertEquals(1, proofNodes.size());
        assertEquals("[(let b2 := false :: $or(true, b2))] ==> [b2]", proofNodes.get(0).getSequent().toString());

        seq = tp.parseSequent("let b3 := true :: let b2 := false :: b3 || b2 |- b2");

        letSub = new LetSubstitutionRule();
        pn = ProofMockUtil.mockProofNode(null, seq.getAntecedent(), seq.getSuccedent());
        parameters = new Parameters();
        parameters.putValue("on", new TermSelector("A.0").selectSubterm(seq));
        parameters.putValue("type", "exhaustive");
        pra = letSub.makeApplication(pn, parameters);
        proofNodes = RuleApplicator.applyRule(pra, pn);
        assertEquals(1, proofNodes.size());
        assertEquals("[$or(true, false)] ==> [b2]", proofNodes.get(0).getSequent().toString());

        seq = tp.parseSequent("i1 + 0 + 1 + 0 |- b2");

        try {
            letSub = DafnyRuleUtil.generateDafnyRuleFromFile("./modules/core/test-res/edu/kit/iti/algover/dafnyrules/addzero.dfy");
        } catch (DafnyRuleException e) {
            System.out.println("Exception occurred during loading dafny rule addzero2.dfy.");
            e.printStackTrace();
        }
        pn = ProofMockUtil.mockProofNode(null, seq.getAntecedent(), seq.getSuccedent());
        parameters = new Parameters();
        parameters.putValue("on", new TermSelector("A.0").selectSubterm(seq));
        parameters.putValue("type", "exhaustive");
        pra = letSub.makeApplication(pn, parameters);
        proofNodes = RuleApplicator.applyRule(pra, pn);
        assertEquals(1, proofNodes.size());
        assertEquals("[$plus($plus(i1, 0), 1)] ==> [b2]", proofNodes.get(0).getSequent().toString());

        seq = tp.parseSequent("i1 + 0 + 1 + 0 |- b2");

        try {
            letSub = DafnyRuleUtil.generateDafnyRuleFromFile("./modules/core/test-res/edu/kit/iti/algover/dafnyrules/addzero.dfy");
        } catch (DafnyRuleException e) {
            System.out.println("Exception corrued during laoding dafny rule addzero2.dfy.");
            e.printStackTrace();
        }
        pn = ProofMockUtil.mockProofNode(null, seq.getAntecedent(), seq.getSuccedent());
        parameters = new Parameters();
        parameters.putValue("on", new TermSelector("A.0").selectSubterm(seq));
        parameters.putValue("type", "deep");
        pra = letSub.makeApplication(pn, parameters);
        proofNodes = RuleApplicator.applyRule(pra, pn);
        assertEquals(1, proofNodes.size());
        assertEquals("[$plus(i1, 1)] ==> [b2]", proofNodes.get(0).getSequent().toString());

    }
}
