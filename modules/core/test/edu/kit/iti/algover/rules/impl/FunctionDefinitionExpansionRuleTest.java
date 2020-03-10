/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.rules.ProofRuleApplication.Applicability;
import edu.kit.iti.algover.rules.TermSelector.SequentPolarity;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuilder;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.ProofMockUtil;
import edu.kit.iti.algover.util.TestUtil;
import org.antlr.runtime.RecognitionException;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;
import org.junit.runner.RunWith;
import junitparams.JUnitParamsRunner;

import java.io.IOException;

import static org.junit.Assert.*;

public class FunctionDefinitionExpansionRuleTest {

    @Rule
    public final ExpectedException exception = ExpectedException.none();

    @Test
    public void testExpansion1Inline() throws Exception {
        String code = "function f(x:int) : int requires x >= 0 { if x ==0 then 0 else f(x-1)+1 }\n" +
                "method m() { assert forall x :: f(x+1) == x+1; }";
        Project p = TestUtil.mockProject(code);
        PVC pvc = p.getPVCByName("m/Assert");
        Sequent seq = pvc.getSequent();
        ProofNode target = new ProofNode(null, null, seq, pvc);
        FunctionDefinitionExpansionRule fder = new FunctionDefinitionExpansionRule();

        ProofRuleApplication application = fder.considerApplication(
                target, seq, new TermSelector(SequentPolarity.SUCCEDENT, 0, 0, 0));

        assertEquals(Applicability.APPLICABLE, application.getApplicability());
        assertEquals(2, application.getBranchCount());
        {
            BranchInfo cont = application.getBranchInfo().get(0);
            assertEquals("continue", cont.getLabel());
            assertTrue(cont.getAdditions().isEmpty());
            assertTrue(cont.getDeletions().isEmpty());
            assertEquals("$ite<int>($eq<int>($plus(x, 1), 0), 0, $plus($$f($heap, $minus($plus(x, 1), 1)), 1))",
                    cont.getReplacements().getLast().snd.toString());
            assertEquals("S.0.0.0",
                    cont.getReplacements().getLast().fst.toString());
        }
        {
            BranchInfo just = application.getBranchInfo().get(1);
            assertEquals("justify", just.getLabel());
            assertTrue(just.getReplacements().isEmpty());
            assertTrue(just.getDeletions().isEmpty());
            assertEquals("|- (forall x:int :: $ge($plus(x, 1), 0))",
                    just.getAdditions().toString());
        }
    }

    @Test
    public void testExpansion1() throws Exception {
        String code = "function f(x:int) : int requires x >= 0 { if x ==0 then 0 else f(x-1)+1 }\n" +
                "method m() { assert forall x :: f(x+1) == x+1; }";
        Project p = TestUtil.mockProject(code);
        PVC pvc = p.getPVCByName("m/Assert");
        Sequent seq = pvc.getSequent();
        ProofNode target = new ProofNode(null, null, seq, pvc);
        FunctionDefinitionExpansionRule fder = new FunctionDefinitionExpansionRule();

        Parameters params = new Parameters();
        params.putValue(FocusProofRule.ON_PARAM_REQ, new TermParameter(new TermSelector(SequentPolarity.SUCCEDENT, 0, 0, 0), seq));
        params.putValue(FunctionDefinitionExpansionRule.INLINE_PARAM, false);
        ProofRuleApplication application = fder.makeApplication(target, params);

        assertEquals(Applicability.APPLICABLE, application.getApplicability());
        assertEquals(2, application.getBranchCount());
        {
            BranchInfo cont = application.getBranchInfo().get(0);
            assertEquals("continue", cont.getLabel());
            assertTrue(cont.getAdditions().isEmpty());
            assertTrue(cont.getDeletions().isEmpty());
            assertEquals("(let heap, x := $heap, $plus(x, 1) :: " +
                            "$ite<int>($eq<int>(x, 0), 0, " +
                            "$plus($$f($heap, $minus(x, 1)), 1)))",
                    cont.getReplacements().getLast().snd.toString());
            assertEquals("S.0.0.0",
                    cont.getReplacements().getLast().fst.toString());
        }
        {
            BranchInfo just = application.getBranchInfo().get(1);
            assertEquals("justify", just.getLabel());
            assertTrue(just.getReplacements().isEmpty());
            assertTrue(just.getDeletions().isEmpty());
            assertEquals("|- (forall x:int :: (let heap, x := $heap, $plus(x, 1) :: $ge(x, 0)))",
                    just.getAdditions().toString());
        }
    }

    @Test
    public void testExpansion2Inline() throws Exception {
        String code = "function f(x:int) : int { if x <= 0 then 0 else f(x-1)+1 }\n" +
                "method m() { assert forall x :: f(x+1) == x+1; }";
        Project p = TestUtil.mockProject(code);
        PVC pvc = p.getPVCByName("m/Assert");
        Sequent seq = pvc.getSequent();
        ProofNode target = new ProofNode(null, null, seq, pvc);
        FunctionDefinitionExpansionRule fder = new FunctionDefinitionExpansionRule();

        ProofRuleApplication application = fder.considerApplication(
                target, seq, new TermSelector(SequentPolarity.SUCCEDENT, 0, 0, 0));

        assertEquals(Applicability.APPLICABLE, application.getApplicability());
        assertEquals(1, application.getBranchCount());
        {
            BranchInfo cont = application.getBranchInfo().get(0);
            assertEquals("continue", cont.getLabel());
            assertTrue(cont.getAdditions().isEmpty());
            assertTrue(cont.getDeletions().isEmpty());
            assertEquals("$ite<int>($le($plus(x, 1), 0), 0, $plus($$f($heap, $minus($plus(x, 1), 1)), 1))",
                    cont.getReplacements().getLast().snd.toString());
            assertEquals("S.0.0.0",
                    cont.getReplacements().getLast().fst.toString());
        }
    }
    @Test
    public void testExpansion2() throws Exception {
        String code = "function f(x:int) : int { if x <= 0 then 0 else f(x-1)+1 }\n" +
                "method m() { assert forall x :: f(x+1) == x+1; }";
        Project p = TestUtil.mockProject(code);
        PVC pvc = p.getPVCByName("m/Assert");
        Sequent seq = pvc.getSequent();
        ProofNode target = new ProofNode(null, null, seq, pvc);
        FunctionDefinitionExpansionRule fder = new FunctionDefinitionExpansionRule();

        Parameters params = new Parameters();
        params.putValue(FocusProofRule.ON_PARAM_REQ, new TermParameter(new TermSelector(SequentPolarity.SUCCEDENT, 0, 0, 0), seq));
        params.putValue(FunctionDefinitionExpansionRule.INLINE_PARAM, false);
        ProofRuleApplication application = fder.makeApplication(target, params);

        assertEquals(Applicability.APPLICABLE, application.getApplicability());
        assertEquals(1, application.getBranchCount());
        {
            BranchInfo cont = application.getBranchInfo().get(0);
            assertEquals("continue", cont.getLabel());
            assertTrue(cont.getAdditions().isEmpty());
            assertTrue(cont.getDeletions().isEmpty());
            assertEquals("(let heap, x := $heap, $plus(x, 1) :: " +
                            "$ite<int>($le(x, 0), 0, " +
                            "$plus($$f($heap, $minus(x, 1)), 1)))",
                    cont.getReplacements().getLast().snd.toString());
            assertEquals("S.0.0.0",
                    cont.getReplacements().getLast().fst.toString());
        }
    }

    @Test
    public void testWrongTermNonAppl() throws Exception {
        String code = "function f(x:int) : int requires x >= 0 { if x ==0 then 0 else f(x-1)+1 }\n" +
                "method m() { assert forall x :: f(x+1) == x+1; }";
        Project p = TestUtil.mockProject(code);
        PVC pvc = p.getPVCByName("m/Assert");
        Sequent seq = pvc.getSequent();
        ProofNode target = new ProofNode(null, null, seq, pvc);
        FunctionDefinitionExpansionRule fder = new FunctionDefinitionExpansionRule();

        // selecting the universal quanifier
        ProofRuleApplication application = fder.considerApplication(
                target, seq, new TermSelector(SequentPolarity.SUCCEDENT, 0));

        assertEquals(Applicability.NOT_APPLICABLE, application.getApplicability());
    }

    @Test
    public void testWrongTermNonFunction() throws Exception {
        String code = "function f(x:int) : int requires x >= 0 { if x ==0 then 0 else f(x-1)+1 }\n" +
                "method m() { assert forall x :: f(x+1) == x+1; }";
        Project p = TestUtil.mockProject(code);
        PVC pvc = p.getPVCByName("m/Assert");
        Sequent seq = pvc.getSequent();
        ProofNode target = new ProofNode(null, null, seq, pvc);
        FunctionDefinitionExpansionRule fder = new FunctionDefinitionExpansionRule();

        // selecting the equality
        ProofRuleApplication application = fder.considerApplication(
                target, seq, new TermSelector(SequentPolarity.SUCCEDENT, 0,0));

        assertEquals(Applicability.NOT_APPLICABLE, application.getApplicability());
    }

    @Test
    public void testCopyContext() throws Exception {
        BuiltinSymbols symbols = new BuiltinSymbols();
        Sequent s = TermParser.parseSequent(symbols,
                "|- ! forall x :: let y,z := 3,x :: exists a :: a+x==y+z");
        TermSelector sel = new TermSelector("S.0.0.0.0.0.0");
        Term tt = new TermBuilder(symbols).tt();

        Object actual = TestUtil.callStatic(FunctionDefinitionExpansionRule.class,
                "copyContext", s, sel, tt);

        assertEquals("(forall x:int :: (let y, z := 3, x :: (forall a:int :: true)))",
                actual.toString());
    }
}