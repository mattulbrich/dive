/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;

import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.nuscript.ScriptException;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuilder;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.TestUtil;
import org.antlr.v4.runtime.misc.ParseCancellationException;
import org.junit.AfterClass;
import org.junit.Assert;
import org.junit.BeforeClass;
import org.junit.Test;

import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;

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

    private Proof makeProof(String termStr) throws Exception {
        BuiltinSymbols symboltable = new BuiltinSymbols();
        TermBuilder tb = new TermBuilder(symboltable);
        MockPVCBuilder pb = new MockPVCBuilder();
        pb.setDeclaration(project.getMethod("m"));
        pb.setSymbolTable(symboltable);
        Term term = TermParser.parse(symboltable, termStr);
        pb.setSequent(Sequent.singleSuccedent(new ProofFormula(term)));
        pb.setPathIdentifier("test");
        pb.setReferenceMap(Collections.emptyMap());
        pb.setProject(project);
        PVC pvc = pb.build();
        return new Proof(project, pvc);
    }

    @Test
    public void getScript() throws Exception {
        Proof p = makeProof("true");
        p.setScriptText("someText");
        assertEquals("someText", p.getScriptText());
        assertEquals(ProofStatus.CHANGED_SCRIPT, p.getProofStatus());
    }

    @Test
    public void positiveFake() throws Exception {
        Proof p = makeProof("true");
        p.setScriptTextAndInterpret("fake close=true;");
        assertEquals(ProofStatus.CLOSED, p.getProofStatus());
        Assert.assertNotNull(p.getProofRoot());
    }

    @Test(expected = ScriptException.class)
    public void negativeFake() throws Exception {
        Proof p = makeProof("true");
        p.setScriptTextAndInterpret("fake close=false;");
        assertEquals(ProofStatus.FAILING, p.getProofStatus());
        Assert.assertNotNull(p.getProofRoot());
        assertAndThrowSingleException(p);
    }

    private void assertAndThrowSingleException(Proof p) throws Exception {
        List<Exception> failures = p.getFailures();
        assertEquals(1, failures.size());
        throw failures.get(0);
    }

    @Test
    public void skip() throws Exception {
        Proof p = makeProof("true");
        p.setScriptTextAndInterpret("skip;");
        TestUtil.assertNoException(p.getFailures());
        assertEquals(ProofStatus.OPEN, p.getProofStatus());
        Assert.assertNotNull(p.getProofRoot());
    }

    @Test(expected = ParseCancellationException.class)
    public void gibberish() throws Exception {
        Proof p = makeProof("true");
        p.setScriptTextAndInterpret("!§$%&");
        assertEquals(ProofStatus.FAILING, p.getProofStatus());
        Assert.assertNotNull(p.getProofRoot());
        assertAndThrowSingleException(p);
    }

    @Test(expected = ParseCancellationException.class)
    public void extraInput() throws Exception {
        Proof p = makeProof("true");
        p.setScriptTextAndInterpret("fake; 123");
        assertEquals(ProofStatus.FAILING, p.getProofStatus());
        Assert.assertNotNull(p.getProofRoot());
        assertAndThrowSingleException(p);
    }

    @Test(expected = ScriptException.class)
    public void illegalParameter() throws Exception {
        Proof p = makeProof("true");
        p.setScriptTextAndInterpret("fake unknownParameter=true;");
        assertEquals(ProofStatus.FAILING, p.getProofStatus());
        Assert.assertNotNull(p.getProofRoot());
        assertAndThrowSingleException(p);
    }

    @Test
    public void schemaOnParameter() throws Exception {
        Proof p = makeProof("let i:=0 ; i >= 0");
        p.setScriptTextAndInterpret("substitute on='|- (?m: _) '; ");
        assertEquals(ProofStatus.OPEN, p.getProofStatus());
        Assert.assertNotNull(p.getProofRoot());
    }

}
