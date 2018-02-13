/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuilder;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.TestUtil;
import org.antlr.runtime.RecognitionException;
import org.junit.AfterClass;
import org.junit.Assert;
import org.junit.BeforeClass;
import org.junit.Test;

public class ProofTest {

    private static Project project;

    @BeforeClass
    public static void setup() throws Exception {
        project = TestUtil.mockProject("method m() ensures true {}");
    }

    @AfterClass
    public static void tearDown() {
        project = null;
    }

    public Proof makeProof(String termStr) throws Exception {
        BuiltinSymbols symboltable = new BuiltinSymbols();
        TermBuilder tb = new TermBuilder(symboltable);
        MockPVCBuilder pb = new MockPVCBuilder();
        pb.setDeclaration(project.getMethod("m"));
        pb.setSymbolTable(symboltable);
        Term term = TermParser.parse(symboltable, termStr);
        pb.setSequent(Sequent.singleSuccedent(new ProofFormula(term)));
        pb.setPathIdentifier("test");
        PVC pvc = pb.build();
        return new Proof(project, pvc);
    }

    @Test
    public void getScript() throws Exception {
        Proof p = makeProof("true");
        p.setScriptText("someText");
        Assert.assertEquals("someText", p.getScript());
        Assert.assertEquals(ProofStatus.CHANGED_SCRIPT, p.getProofStatus());
    }

    @Test
    public void positiveFake() throws Exception {
        Proof p = makeProof("true");
        p.setScriptTextAndInterpret("fake close=true;");
        Assert.assertEquals(ProofStatus.CLOSED, p.getProofStatus());
        Assert.assertNotNull(p.getProofRoot());
    }

    @Test
    public void negativeFake() throws Exception {
        Proof p = makeProof("true");
        p.setScriptTextAndInterpret("fake close=false;");
        Assert.assertEquals(ProofStatus.OPEN, p.getProofStatus());
        Assert.assertNotNull(p.getProofRoot());
    }

    @Test(expected = org.antlr.v4.runtime.RecognitionException.class)
    public void gibberish() throws Exception {
        Proof p = makeProof("true");
        p.setScriptTextAndInterpret("!§$%&");
        Assert.assertEquals(ProofStatus.FAILING, p.getProofStatus());
        Assert.assertNotNull(p.getProofRoot());
        throw p.getFailException();
    }

    @Test
    public void extraInput() throws Exception {
        Proof p = makeProof("true");
        p.setScriptTextAndInterpret("fake; 123");
        Assert.assertEquals(ProofStatus.FAILING, p.getProofStatus());
        if(TestUtil.VERBOSE)
            p.getFailException().printStackTrace();
        Assert.assertNotNull(p.getFailException());
        Assert.assertNotNull(p.getProofRoot());
    }

    @Test
    public void illegalParameter() throws Exception {
        Proof p = makeProof("true");
        p.setScriptTextAndInterpret("fake unknownParameter=true;");
        Assert.assertEquals(ProofStatus.FAILING, p.getProofStatus());
        Assert.assertNotNull(p.getFailException());
        Assert.assertNotNull(p.getProofRoot());
        if(TestUtil.VERBOSE)
            p.getFailException().printStackTrace();
    }

}