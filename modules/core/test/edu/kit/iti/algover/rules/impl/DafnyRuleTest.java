/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.builder.TreeTermTranslator;
import edu.kit.iti.algover.term.builder.TreeTermTranslatorTest;
import edu.kit.iti.algover.util.FormatException;
import edu.kit.iti.algover.util.ProofMockUtil;
import edu.kit.iti.algover.util.TestUtil;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertSame;
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

        DafnyTree t1 = TreeTermTranslatorTest.parse("b + 0 > 0");
        DafnyTree t2 = TreeTermTranslatorTest.parse("c + d > 0");


        List<ProofFormula> ante = new ArrayList<>();
        List<ProofFormula> dece = new ArrayList<>();
        // REVIEW: This is not a boolean term used as proof formula here.
        ante.add(new ProofFormula(ttt.build(t1)));
        dece.add(new ProofFormula(ttt.build(t2)));

        testSequent = new Sequent(ante, dece);
    }


    @Test
    public void initializationTest() throws DafnyRuleException{
        String dir = System.getProperty("user.dir");
        //System.out.println("current dir = " + dir);
        String file = "test-res/edu/kit/iti/algover/dafnyrules/addzero.dfy";
        DafnyRule r = DafnyRuleUtil.generateDafnyRuleFromFile(file);
        Assert.assertEquals("addZero", r.getName());
    }

    @Test
    public void basicApplicationAddZeroTest() throws RuleException, DafnyRuleException, TermBuildException, FormatException {
        String file = "test-res/edu/kit/iti/algover/dafnyrules/addzero.dfy";

        ProofRule dafnyRule = DafnyRuleUtil.generateDafnyRuleFromFile(file);
        ProofNode pn = ProofMockUtil.mockProofNode(null, testSequent.getAntecedent(), testSequent.getSuccedent());

        TermSelector ts = new TermSelector(TermSelector.SequentPolarity.ANTECEDENT, 0, 0);
        Parameters params = new Parameters();
        params.putValue(dafnyRule.getOnParameter(), new TermParameter(new TermSelector("A.0.0"), testSequent));

        ProofRuleApplication pra = dafnyRule.considerApplication(pn, testSequent, ts);
        assertEquals(pra.getApplicability(), ProofRuleApplication.Applicability.APPLICABLE);
        assertEquals("addZero on='... ((?match: b + 0)) ... |-';", pra.getScriptTranscript());

        pra = dafnyRule.makeApplication(pn, params);
        List<ProofNode> newNodes = RuleApplicator.applyRule(pra, null, pn);

        assertTrue(newNodes.size() == 1);
        assertEquals("$gt(b, 0) |- $gt($plus(c, d), 0)", newNodes.get(0).getSequent().toString());
    }

    @Test
    public void basicApplicationCommAddTest() throws RuleException, DafnyRuleException, TermBuildException, FormatException  {
        String file = "test-res/edu/kit/iti/algover/dafnyrules/commutativeAddition.dfy";
        ProofRule dafnyRule = DafnyRuleUtil.generateDafnyRuleFromFile(file);
        ProofNode pn = ProofMockUtil.mockProofNode(null, testSequent.getAntecedent(), testSequent.getSuccedent());

        TermSelector ts = new TermSelector(TermSelector.SequentPolarity.SUCCEDENT, 0, 0);
        Parameters params = new Parameters();
        params.putValue(dafnyRule.getOnParameter(), new TermParameter(new TermSelector("S.0.0"), testSequent));

        ProofRuleApplication pra = dafnyRule.considerApplication(pn, testSequent, ts);
        assertEquals(pra.getApplicability(), ProofRuleApplication.Applicability.APPLICABLE);
        assertEquals("commAddition on='|- ... ((?match: c + d)) ...';", pra.getScriptTranscript());

        pra = dafnyRule.makeApplication(pn, params);
        List<ProofNode> newNodes = RuleApplicator.applyRule(pra, null, pn);

        assertTrue(newNodes.size() == 1);
        assertEquals("$gt($plus(b, 0), 0) |- $gt($plus(d, c), 0)", newNodes.get(0).getSequent().toString());
    }

    // was a bug
    @Test
    public void testNameConflict() throws Exception {

        Project project = TestUtil.mockProject("lemma l1() ensures (1==2) == false {} method m() ensures 1==2 {}");

        PVC pvc = project.getPVCByName("m/Post");
        Collection<ProofRule> rules = project.getProofRules(pvc);
        DafnyRule l1Rule = null;
        for (ProofRule rule : rules) {
            if(rule.getName().equals("l1")) {
                l1Rule = (DafnyRule) rule;
                break;
            }
        }

        FunctionSymbol eqInSearchTerm = ((ApplTerm) l1Rule.getSearchTerm()).getFunctionSymbol();
        assertEquals("$eq<int>(int, int) : bool", eqInSearchTerm.toString());

        FunctionSymbol eqInPostCond = ((ApplTerm) pvc.getSequent().getSuccedent().get(0).getTerm()).getFunctionSymbol();
        assertEquals("$eq<int>(int, int) : bool", eqInPostCond.toString());

        assertSame(eqInPostCond, eqInSearchTerm);
    }

    // was a bug
    @Test
    public void testIllegalVariables() throws Exception {
        Project project = TestUtil.mockProject("lemma l1(s: seq<int>) ensures (|s|==|s|) {}");
        DafnyRule l1Rule = null;
        for (ProofRule rule : project.getAllProofRules()) {
            if(rule.getName().equals("l1")) {
                l1Rule = (DafnyRule) rule;
                break;
            }
        }
        assertNotNull(l1Rule);
        assertEquals("$seqLen<int>(s)", l1Rule.getSearchTerm().toString());
        assertEquals("$seqLen<int>(s)", l1Rule.getReplaceTerm().toString());
    }
}
