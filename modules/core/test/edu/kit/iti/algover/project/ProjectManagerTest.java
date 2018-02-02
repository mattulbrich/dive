/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.project;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.PVCCollection;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofStatus;
import edu.kit.iti.algover.script.exceptions.ScriptCommandNotApplicableException;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.parser.TermParser;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;

import static org.junit.Assert.assertTrue;

/**
 * Tests for the methods for ProjectManagement
 */
public class ProjectManagerTest {

    private static final String testDir = "modules/core/test-res/edu/kit/iti/algover/script".replace('/', File.separatorChar);
    private static final String config = "config2.xml";

    Project p = null;
    Term testTerm;
    String testPVCName = "m1/Post";
    String testPVC2Name = "x/Post";
    String testPVC2 = "x/Post";
    ProjectManager pm = null;

    @Before
    public void prepare() throws Exception {

        final File f1 = new File(testDir);

        ProjectBuilder pb = new ProjectBuilder();
        pb.setDir(f1);
        pb.setConfigFilename(config);
        pb.parseProjectConfigurationFile();
        Project p = pb.build();
        this.p = p;
        makeTestTerm();

    }

    private void makeTestTerm() throws DafnyParserException {
        Collection<FunctionSymbol> map = new ArrayList<>();
        SymbolTable symbTable = new MapSymbolTable(new BuiltinSymbols(), map);
        this.testTerm = TermParser.parse(symbTable, "1==2 && 2==3");
    }



    @Test
    public void loadExistingProject() throws Exception {
        // REVIEW: Why is pm a field in the class.
        pm = new ProjectManager(new File(testDir), config);
        Project project = pm.getProject();

        Assert.assertEquals("Number of DafnyFiles", p.getDafnyFiles().size(), project.getDafnyFiles().size());
        Assert.assertEquals("config2.xml", pm.getConfigFilename());

        PVCCollection allPVCs = project.getAllPVCs();
        PVC testPVC = project.getPVCByName(testPVC2Name);

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

        Proof proof = pm.getProofForPVC(testPVC2Name);

        Assert.assertNotNull(proof.getScript());
//        pm.initializeProofDataStructures(testPVCName);
        // pm.findAndParseScriptFileForPVC(testPVCName);

        Assert.assertEquals("Proofscript is parsed", ProofStatus.CHANGED_SCRIPT, proof.getProofStatus());

        proof.interpretScript();
        Assert.assertEquals("Proofscript has run", ProofStatus.OPEN, proof.getProofStatus());

        System.out.println("Proof root for PVC " + testPVC2Name + " \n" + pm.getProofForPVC(testPVC2).getProofRoot().getSequent());

        //get the Proof object for a PVC
        Proof proof2 = pm.getProofForPVC(testPVC2);

        //Assert.assertEquals("Proofscript is not loaded yet", ProofStatus.NOT_LOADED, proof2.getProofStatus());

        //find and parse a script file for PVC
        String script = pm.loadScriptForPVC(testPVC2);
        pm.getProofForPVC(testPVC2).setScriptText(script);

        //System.out.println("Current State " + proof.getInterpreter().getCurrentState().getSelectedGoalNode());
        //pm.replayAllProofs();

        //this should be the way a script should be interpreted
        proof2.interpretScript();
        //the way to print the proof tree
        //proof2.getProofRoot();
        System.out.println(proof2.proofToString());
        // proof2.invalidate();

        String newScript = "//substitute on='let $mod := $everything :: (let x := 1 :: 1== 2 && 2 == 3 && 4==5)';\n" +
                "//substitute on='let x := 1 :: 1== 2 && 2 == 3 &&4==5 '; \n" +
                "x:int := 0; \n" +
                "andRight on='1== 2 && 2 == 3 &&4==5';\n";
        //set a new script text and parse it
        proof2.setScriptText(newScript);
        System.out.println(proof2.getScript());
        //interpret new Script
        proof2.interpretScript();


        pm.getAllProofs().forEach((s1, proof1) -> {
            proof1.invalidate();
        });
        Proof proofAfter = pm.getProofForPVC(testPVCName);

        System.out.println(proofAfter.getScript().toString());
        Assert.assertNotNull(proofAfter.getScript());
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
    @Test(expected = ScriptCommandNotApplicableException.class)
    public void testInapplicableScriptCommand() throws ScriptCommandNotApplicableException, Exception {
        pm = new ProjectManager(new File(testDir), config);

        Proof proof = pm.getProofForPVC(testPVCName);

        proof.setScriptTextAndInterpret("substitute on='true';");
    }

    // This test currently fails with a NullPointerException, but I felt like an empty script should be
    // interpretable, even though it doesn't advance the proof state...
    @Test
    public void testEmptyScript() throws Exception {
        pm = new ProjectManager(new File(testDir), config);

        Proof proof = pm.getProofForPVC(testPVCName);

        proof.setScriptTextAndInterpret(" ");
        assertTrue(proof.getProofRoot().getChildren().isEmpty());

        proof.setScriptTextAndInterpret(" /* empty script */ ");
        assertTrue(proof.getProofRoot().getChildren().isEmpty());
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

}
