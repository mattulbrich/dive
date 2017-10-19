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

/**
 * Tests for the methods for ProjectManagement
 */
public class ProjectManagerTest {

    static final String testDir = ("modules/core/test-res/edu/kit/iti/algover/script").replace('/', File.separatorChar);
    static final File config = new File(testDir + File.separatorChar + "config2.xml");
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
        pb.setConfigFilename("config2.xml");
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


    @Ignore
    @Test
    public void loadExistingProject() throws Exception {
        pm = new ProjectManager();
        pm.loadProject(config);
        Project project = pm.getProject();

        Assert.assertEquals("Number of DafnyFiles", p.getDafnyFiles().size(), project.getDafnyFiles().size());
        Assert.assertEquals("config2.xml", pm.getConfigFile().getName());

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

        Assert.assertEquals("Proofscript is parsed", ProofStatus.SCRIPT_PARSED, proof.getProofStatus());

        Proof proof2 = pm.getProofForPVC(testPVC2);
        //  Assert.assertEquals("Proofscript is not loaded yet", ProofStatus.NOT_LOADED, proof2.getProofStatus());
        //  pm.findAndParseScriptFileForPVC(testPVC2);

        //System.out.println("Current State " + proof.getInterpreter().getCurrentState().getSelectedGoalNode());
        //pm.replayAllProofs();

        //this should be the way a script should be applied
        System.out.println(proof2.interpretScript());

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
