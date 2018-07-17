package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.builder.TreeTermTranslator;
import edu.kit.iti.algover.term.builder.TreeTermTranslatorTest;
import edu.kit.iti.algover.util.ProofMockUtil;
import org.junit.Before;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * Created by jklamroth on 1/17/18.
 */
public class OrLeftRuleTest {
    SymbolTable symbTable;
    Sequent testSequent;

    @Before
    public void setup() throws TermBuildException, org.antlr.runtime.RecognitionException {
        Collection<FunctionSymbol> map = new ArrayList<>();
        map.add(new FunctionSymbol("b1", Sort.BOOL));
        map.add(new FunctionSymbol("b2", Sort.BOOL));
        map.add(new FunctionSymbol("b3", Sort.BOOL));
        symbTable = new MapSymbolTable(new BuiltinSymbols(), map);

        TreeTermTranslator ttt = new TreeTermTranslator(symbTable);

        DafnyTree t1 = TreeTermTranslatorTest.parse("b1 || b2");
        DafnyTree t2 = TreeTermTranslatorTest.parse("b3");
        DafnyTree t3 = TreeTermTranslatorTest.parse("b2 || b1");
        DafnyTree t4 = TreeTermTranslatorTest.parse("b3");

        List<ProofFormula> ante = new ArrayList<>();
        List<ProofFormula> dece = new ArrayList<>();
        ante.add(new ProofFormula(ttt.build(t1)));
        ante.add(new ProofFormula(ttt.build(t4)));
        dece.add(new ProofFormula(ttt.build(t2)));
        dece.add(new ProofFormula(ttt.build(t3)));

        testSequent = new Sequent(ante, dece);
        System.out.println("testSequent = " + testSequent);

    }


    @Test
    public void basicTest() throws RuleException, TermBuildException {
        ProofRule orLeftRule = new OrLeftRule();
        ProofNode pn = ProofMockUtil.mockProofNode(null, testSequent.getAntecedent(), testSequent.getSuccedent());

        TermSelector ts = new TermSelector(TermSelector.SequentPolarity.ANTECEDENT, 0);
        Parameters params = new Parameters();
        params.putValue("on", testSequent.getAntecedent().get(0).getTerm());

        ProofRuleApplication pra = orLeftRule.considerApplication(pn, testSequent, ts);
        assertEquals(pra.getApplicability(), ProofRuleApplication.Applicability.APPLICABLE);
//        assertEquals(pra.getScriptTranscript(), "orLeft on='" + testSequent.getAntecedent().get(0).getTerm() + "';");

        pra = orLeftRule.makeApplication(pn, params);
        List<ProofNode> newNodes = RuleApplicator.applyRule(pra, pn);

        assertTrue(newNodes.size() == 2);
        assertEquals("b1, b3 |- b3, $or(b2, b1)", newNodes.get(0).getSequent().toString());
        assertEquals("b2, b3 |- b3, $or(b2, b1)", newNodes.get(1).getSequent().toString());
    }

    @Test
    public void notApplicableTest() throws RuleException, TermBuildException {
        ProofRule orLeftRule = new OrLeftRule();
        ProofNode pn = ProofMockUtil.mockProofNode(null, testSequent.getAntecedent(), testSequent.getSuccedent());

        TermSelector ts = new TermSelector(TermSelector.SequentPolarity.SUCCEDENT, 1);

        ProofRuleApplication pra = orLeftRule.considerApplication(pn, testSequent, ts);
        assertEquals(pra.getApplicability(), ProofRuleApplication.Applicability.NOT_APPLICABLE);

        ts = new TermSelector(TermSelector.SequentPolarity.SUCCEDENT, 0);

        pra = orLeftRule.considerApplication(pn, testSequent, ts);
        assertEquals(pra.getApplicability(), ProofRuleApplication.Applicability.NOT_APPLICABLE);

        ts = new TermSelector(TermSelector.SequentPolarity.ANTECEDENT, 1);

        pra = orLeftRule.considerApplication(pn, testSequent, ts);
        assertEquals(pra.getApplicability(), ProofRuleApplication.Applicability.NOT_APPLICABLE);
    }

    @Test(expected = RuleException.class)
    public void throwExceptionTest() throws RuleException, TermBuildException {
        ProofRule orLeftRule = new OrLeftRule();
        ProofNode pn = ProofMockUtil.mockProofNode(null, testSequent.getAntecedent(), testSequent.getSuccedent());

        Parameters params = new Parameters();
        params.putValue("on", testSequent.getAntecedent().get(1).getTerm());

        orLeftRule.makeApplication(pn, params);
    }

    @Test(expected = RuleException.class)
    public void throwExceptionTest1() throws RuleException, TermBuildException {
        ProofRule orLeftRule = new OrLeftRule();
        ProofNode pn = ProofMockUtil.mockProofNode(null, testSequent.getAntecedent(), testSequent.getSuccedent());

        Parameters params = new Parameters();
        params.putValue("on", testSequent.getSuccedent().get(1).getTerm());

        orLeftRule.makeApplication(pn, params);
    }
}
