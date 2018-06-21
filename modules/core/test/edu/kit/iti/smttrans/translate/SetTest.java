package edu.kit.iti.smttrans.translate;

import java.io.File;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.project.ProjectBuilder;
import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.PVCCollection;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofStatus;
import edu.kit.iti.algover.term.Sequent;

public class SetTest {

    private static final String pDir = "modules/core/test-res/edu/kit/iti/algover/smttrans".replace('/', File.separatorChar);
    private static final String config = "setsconfig.xml";

    Project p = null;
//    Term testTerm;
    String setOpPost = "setOP/Post";
    String intersectPost = "intersect/Post";

    @Before
    public void prepare() throws Exception {

        final File f1 = new File(pDir);

        ProjectBuilder pb = new ProjectBuilder();
        pb.setDir(f1);
        pb.setConfigFilename(config);
        pb.parseProjectConfigurationFile();
        Project p = pb.build();
        this.p = p;
//        makeTestTerm();

    }

//    private void makeTestTerm() throws Exception {
//        Collection<FunctionSymbol> map = new ArrayList<>();
//        SymbolTable symbTable = new MapSymbolTable(new BuiltinSymbols(), map);
//        this.testTerm = TermParser.parse(symbTable, "1==2 && 2==3");
//    }



    @Test
    public void loadExistingProject() throws Exception {
        ProjectManager pm = new ProjectManager(new File(pDir), config);
        Project project = pm.getProject();

        Assert.assertEquals("Number of DafnyFiles", p.getDafnyFiles().size(), project.getDafnyFiles().size());
        Assert.assertEquals("setsconfig.xml", pm.getConfigFilename());

        PVCCollection allPVCs = project.getAllPVCs();
        PVC testPVC = project.getPVCByName(intersectPost);

        Sequent s = testPVC.getSequent();

       Assert.assertFalse("Sequents antecedent is not empty", s.getAntecedent().isEmpty());
        Assert.assertFalse("Sequents succedent is not empty", s.getSuccedent().isEmpty());

   //     Term sequentTerm = s.getSuccedent().get(0).getTerm();
   //     Term t = sequentTerm.getSubterms().get(0);

//        System.out.println(t.getSubterms());
//        System.out.println(testTerm.getSubterms());
//        //subterm is "true"
//        Assert.assertEquals(t.getSort(), testTerm.getSort());
//        Assert.assertEquals(2, t.getSubterms().size());

        Proof proof = pm.getProofForPVC(intersectPost);

        Assert.assertNotNull(proof.getScript());
//        pm.initializeProofDataStructures(testPVCm1Post);
        // pm.findAndParseScriptFileForPVC(testPVCm1Post);

        Assert.assertEquals("Proofscript is parsed", ProofStatus.CHANGED_SCRIPT, proof.getProofStatus());
        Assert.assertNull(proof.getFailException());

        proof.interpretScript();
        Assert.assertEquals("Proofscript has run", ProofStatus.OPEN, proof.getProofStatus());
        Assert.assertNull(proof.getFailException());

        System.out.println("Proof root for PVC " + intersectPost + " \n" + pm.getProofForPVC(intersectPost).getProofRoot().getSequent());

        //get the Proof object for a PVC
        Proof proof2 = pm.getProofForPVC(intersectPost);

        //Assert.assertEquals("Proofscript is not loaded yet", ProofStatus.NOT_LOADED, proof2.getProofStatus());

        //find and parse a script file for PVC
        String script = pm.loadScriptForPVC(intersectPost);
        pm.getProofForPVC(intersectPost).setScriptText(script);

        //System.out.println("Current State " + proof.getInterpreter().getCurrentState().getSelectedGoalNode());
        //pm.replayAllProofs();

        //this should be the way a script should be interpreted
        proof2.interpretScript();
        Assert.assertNull(proof.getFailException());

        //the way to print the proof tree
        //proof2.getProofRoot();
        System.out.println(proof2.proofToString());
        // proof2.invalidate();

//        String newScript = "//substitute on='let $mod := $everything :: (let x := 1 :: 1== 2 && 2 == 3 && 4==5)';\n" +
//                "//substitute on='let x := 1 :: 1== 2 && 2 == 3 &&4==5 '; \n" +
//                "x:int := 0; \n" +
//                "andRight on='1== 2 && 2 == 3 &&4==5';\n";
//        
        String newScript = "z3";
        
        
        //set a new script text and parse it
        proof2.setScriptText(newScript);
        System.out.println(proof2.getScript());
        //interpret new Script
        proof2.interpretScript();
        Assert.assertNull(proof.getFailException());

        pm.getAllProofs().forEach((s1, proof1) -> {
            proof1.invalidate();
        });
        Proof proofAfter = pm.getProofForPVC(setOpPost);

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




}
