package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyException;
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
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * Created by jklamroth on 1/25/18.
 */
public class DafnyRuleTest {
    SymbolTable symbTable;
    Sequent testSequent;

    @Before
    public void setup() throws TermBuildException, org.antlr.runtime.RecognitionException {
        Collection<FunctionSymbol> map = new ArrayList<>();
        map.add(new FunctionSymbol("b", Sort.INT));
        map.add(new FunctionSymbol("c", Sort.INT));
        map.add(new FunctionSymbol("d", Sort.INT));
        symbTable = new MapSymbolTable(new BuiltinSymbols(), map);

        TreeTermTranslator ttt = new TreeTermTranslator(symbTable);

        DafnyTree t1 = TreeTermTranslatorTest.parse("b + 0");
        DafnyTree t2 = TreeTermTranslatorTest.parse("c + d");


        List<ProofFormula> ante = new ArrayList<>();
        List<ProofFormula> dece = new ArrayList<>();
        ante.add(new ProofFormula(ttt.build(t1)));
        dece.add(new ProofFormula(ttt.build(t2)));

        testSequent = new Sequent(ante, dece);
    }


    @Test
    public void initializationTest() throws DafnyRuleException{
        String dir = System.getProperty("user.dir");
        //System.out.println("current dir = " + dir);
        String file = "./modules/core/test-res/edu/kit/iti/algover/dafnyrules/addzero.dfy";
        DafnyRule r = DafnyRuleUtil.generateDafnyRuleFromFile(file);
        Assert.assertEquals("addZero", r.getName());
    }

    @Test
    public void basicApplicationAddZeroTest() throws RuleException, DafnyRuleException, TermBuildException {
        String file = "./modules/core/test-res/edu/kit/iti/algover/dafnyrules/addzero.dfy";

        ProofRule dafnyRule = DafnyRuleUtil.generateDafnyRuleFromFile(file);
        ProofNode pn = ProofMockUtil.mockProofNode(null, testSequent.getAntecedent(), testSequent.getSuccedent());

        TermSelector ts = new TermSelector(TermSelector.SequentPolarity.ANTECEDENT, 0);
        Parameters params = new Parameters();
        params.putValue("on", testSequent.getAntecedent().get(0).getTerm());

        ProofRuleApplication pra = dafnyRule.considerApplication(pn, testSequent, ts);
        assertEquals(pra.getApplicability(), ProofRuleApplication.Applicability.APPLICABLE);
        assertEquals("addZero on='b + 0';", pra.getScriptTranscript());

        pra = dafnyRule.makeApplication(pn, params);
        List<ProofNode> newNodes = RuleApplicator.applyRule(pra, pn);

        assertTrue(newNodes.size() == 1);
        assertEquals("[b] ==> [$plus(c, d)]", newNodes.get(0).getSequent().toString());
    }

    @Test
    public void basicApplicationCommAddTest() throws RuleException, DafnyRuleException, TermBuildException  {
        String file = "./modules/core/test-res/edu/kit/iti/algover/dafnyrules/commutativeAddition.dfy";
        ProofRule dafnyRule = DafnyRuleUtil.generateDafnyRuleFromFile(file);
        ProofNode pn = ProofMockUtil.mockProofNode(null, testSequent.getAntecedent(), testSequent.getSuccedent());

        TermSelector ts = new TermSelector(TermSelector.SequentPolarity.SUCCEDENT, 0);
        Parameters params = new Parameters();
        params.putValue("on", testSequent.getSuccedent().get(0).getTerm());

        ProofRuleApplication pra = dafnyRule.considerApplication(pn, testSequent, ts);
        assertEquals(pra.getApplicability(), ProofRuleApplication.Applicability.APPLICABLE);
        assertEquals("commAddition on='c + d';", pra.getScriptTranscript());

        pra = dafnyRule.makeApplication(pn, params);
        List<ProofNode> newNodes = RuleApplicator.applyRule(pra, pn);

        assertTrue(newNodes.size() == 1);
        assertEquals("[$plus(b, 0)] ==> [$plus(d, c)]", newNodes.get(0).getSequent().toString());
    }
}
