package edu.kit.iti.algover.rules.impl;

import antlr.RecognitionException;
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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;

/**
 * Created by jklamroth on 1/17/18.
 */
public class NotLeftRuleTest {
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
        DafnyTree t2 = TreeTermTranslatorTest.parse("b1");
        DafnyTree t3 = TreeTermTranslatorTest.parse("b2");

        List<ProofFormula> ante = new ArrayList<>();
        List<ProofFormula> dece = new ArrayList<>();
        ante.add(new ProofFormula(ttt.build(t1)));
        dece.add(new ProofFormula(ttt.build(t2)));
        dece.add(new ProofFormula(ttt.build(t3)));

        testSequent = new Sequent(ante, dece);

    }


    @Test
    public void basicTest() throws RuleException, TermBuildException {
        ProofRule notLeftRule = new NotLeftRule();
        ProofNode pn = ProofMockUtil.mockProofNode(null, testSequent.getAntecedent(), testSequent.getSuccedent());

        TermSelector ts = new TermSelector(TermSelector.SequentPolarity.ANTECEDENT, 0);
        Parameters params = new Parameters();
        params.putValue("on", testSequent.getAntecedent().get(0).getTerm());

        notLeftRule.considerApplication(pn, testSequent, ts);
        ProofRuleApplication pra = notLeftRule.makeApplication(pn, params);
        List<ProofNode> newNodes = RuleApplicator.applyRule(pra, pn);
        assertTrue(newNodes.size() == 1);

        assertEquals("[] ==> [b1, b2, $not($or(b1, b2))]", newNodes.get(0).getSequent().toString());
    }


}
