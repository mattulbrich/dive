/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.project;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.nuscript.ScriptException;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.PVCCollection;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofStatus;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.parser.TermParser;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;

import static org.junit.Assert.assertTrue;

/**
 * Tests for the methods for ProjectManagement
 */
public class ProjectManagerTest {

    private static final String testDir = "test-res/edu/kit/iti/algover/script".replace('/', File.separatorChar);
    private static final String config = "config2.xml";

    Project p = null;
    Term testTerm;
    String testPVCm1Post = "m1/Post";
    String testPVCxPost = "x/Post";

    @Before
    public void prepare() throws Exception {

        final File f1 = new File(testDir);

        XMLProjectManager pm = new XMLProjectManager(f1, config);
        pm.reload();
        Project p = pm.getProject();
        this.p = p;
        makeTestTerm();

    }

    private void makeTestTerm() throws Exception {
        Collection<FunctionSymbol> map = new ArrayList<>();
        SymbolTable symbTable = new MapSymbolTable(new BuiltinSymbols(), map);
        this.testTerm = TermParser.parse(symbTable, "1==2 && 2==3");
    }

    @Test
    public void loadExistingProject() throws Exception {
        XMLProjectManager pm = new XMLProjectManager(new File(testDir), config);
        pm.reload();
        Project project = pm.getProject();

        Assert.assertEquals("Number of DafnyFiles", p.getDafnyFiles().size(), project.getDafnyFiles().size());
        Assert.assertEquals("config2.xml", pm.getConfigFilename());

        PVCCollection allPVCs = project.getAllPVCs();
        PVC testPVC = project.getPVCByName(testPVCxPost);

        Sequent s = testPVC.getSequent();

        Assert.assertTrue("Sequents antecedent is empty", testPVC.getSequent().getAntecedent().isEmpty());
        Assert.assertFalse("Sequents succedent is not empty", testPVC.getSequent().getSuccedent().isEmpty());

        Term sequentTerm = s.getSuccedent().get(0).getTerm();
        Term t = sequentTerm.getSubterms().get(0);

        System.out.println(t.getSubterms());
        System.out.println(testTerm.getSubterms());
        //subterm is "true"
        Assert.assertEquals(t.getSort(), testTerm.getSort());
        Assert.assertEquals(2, t.getSubterms().size());

        Proof proof = pm.getProofForPVC(testPVCxPost);

        Assert.assertNotNull(proof.getScriptText());
//        pm.initializeProofDataStructures(testPVCm1Post);
        // pm.findAndParseScriptFileForPVC(testPVCm1Post);
       // Assert.assertTrue();
        Assert.assertEquals("Proofscript is parsed", ProofStatus.CHANGED_SCRIPT, proof.getProofStatus());
        Assert.assertNull(proof.getFailException());
        Assert.assertTrue(proof.getDfyFile() != null);

        proof.interpretScript();

        Assert.assertEquals("Proofscript has run", ProofStatus.OPEN, proof.getProofStatus());
        Assert.assertNull(proof.getFailException());

        System.out.println("Proof root for PVC " + testPVCxPost + " \n" + pm.getProofForPVC(testPVCxPost).getProofRoot().getSequent());
        //get the Proof object for a PVC
        Proof proof2 = pm.getProofForPVC(testPVCxPost);

        //Assert.assertEquals("Proofscript is not loaded yet", ProofStatus.NOT_LOADED, proof2.getProofStatus());

        //find and parse a script file for PVC
        String script = pm.loadScriptForPVC(testPVCxPost);
        pm.getProofForPVC(testPVCxPost).setScriptText(script);

        //System.out.println("Current State " + proof.getInterpreter().getCurrentState().getSelectedGoalNode());
        //pm.replayAllProofs();

        //this should be the way a script should be interpreted
        proof2.interpretScript();
        Assert.assertNull(proof.getFailException());

        //the way to print the proof tree
        //proof2.getProofRoot();
        System.out.println(proof2.proofToString());
        // proof2.invalidate();

        String newScript = "//substitute on='let $mod := $everything :: (let x := 1 :: 1== 2 && 2 == 3 && 4==5)';\n" +
                "//substitute on='let x := 1 :: 1== 2 && 2 == 3 &&4==5 '; \n" +
                "x:int := 0; \n" +
                "andRight on='1== 2 && 2 == 3 && 4==5';\n";
        //set a new script text and parse it
        proof2.setScriptText(newScript);
        System.out.println(proof2.getScriptText());
        //interpret new Script
        proof2.interpretScript();
        Assert.assertNull(proof.getFailException());
        System.out.println(proof2.getDfyFile().getFilename() + proof2.getGraph().toString());
        pm.getAllProofs().forEach((s1, proof1) -> {
            proof1.invalidate();
        });
        Proof proofAfter = pm.getProofForPVC(testPVCm1Post);


        System.out.println(proofAfter.getScriptText().toString());
        Assert.assertNotNull(proofAfter.getScriptText());
        Assert.assertEquals("Proof is not loaded yet", ProofStatus.DIRTY, proof.getProofStatus());

        pm.saveProject();
        //Assert.assertEquals(Status.DIRTY, proof.getStatus());
       /* pm.replayAllProofs();
        for (Proof pr : pm.getAllProofs().values()) {
            Assert.assertEquals(ProofStatus.NON_EXISTING, pr.getProofStatus());
        }*/

    }

    // This test currently throws a NullPointerException, instead of the ScriptCommandNotApplicable exception.
    // That exception is caught during execution at some point and during catching, a NullPointerException is
    // generated. The point that happens is marked via "TODO handling of error state for each visit".
    @Test(expected = ScriptException.class)
    public void testInapplicableScriptCommand() throws Exception {
        ProjectManager pm = new XMLProjectManager (new File(testDir), config);
        pm.reload();

        Proof proof = pm.getProofForPVC(testPVCm1Post);

        proof.setScriptTextAndInterpret("substitute on='true';");
        throw proof.getFailException();
    }

    // This test currently fails with a NullPointerException, but I felt like an empty script should be
    // interpretable, even though it doesn't advance the proof state...
    @Test
    public void testEmptyScript() throws Exception {
        ProjectManager pm = new XMLProjectManager(new File(testDir), config);
        pm.reload();

        Proof proof = pm.getProofForPVC(testPVCm1Post);

        proof.setScriptTextAndInterpret(" ");
        assertTrue(proof.getProofRoot().getChildren().isEmpty());
        if (proof.getFailException() != null)
            proof.getFailException().printStackTrace();
        Assert.assertNull(proof.getFailException());

        proof.setScriptTextAndInterpret(" /* empty script */ ");
        assertTrue(proof.getProofRoot().getChildren().isEmpty());
        Assert.assertNull(proof.getFailException());
    }

    @Test
    public void userChangedSourceCode() {
        //ProjectManagement.saveFile(File, content);
        //Proof Management saveProject();
        //ProofManagement.saveVersion();
        //ProofManagement.getAllProofs.setStatus(Dirty)
    }

    @Test
    public void userChangedScript() {

        //ProjectManagement.saveScriptFile(pvcid, content);
        //Proof Management saveProject();
        //ProofManagment.saveVersion();
        //ProofManagement.getProofForPVC(pvcid).setStatus(Dirty)
        //ProofManagement.replayProofs();s

    }

    @Test
    public void interpretScriptExhaustiveRules() throws Exception {
        ProjectManager pm = new XMLProjectManager(new File(testDir), "configsum.xml");
        pm.reload();
        Proof proof = pm.getProofForPVC("sumAndMax/loop/else/Inv");
        proof.interpretScript(); //Hier Zeile die exhaustive sein soll einfuegen

        if (proof.getFailException() != null)
            proof.getFailException().printStackTrace();
    }

}
