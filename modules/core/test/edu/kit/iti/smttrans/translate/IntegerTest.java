package edu.kit.iti.smttrans.translate;

import static java.util.Arrays.asList;

import java.io.File;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.junit.Assert;
import org.junit.Test;

import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.PVCCollection;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofStatus;
import edu.kit.iti.algover.rules.impl.Z3Rule;
import edu.kit.iti.algover.script.exceptions.ScriptCommandNotApplicableException;
import edu.kit.iti.algover.smttrans.access.Model;

public class IntegerTest {
    private static final String dir = "modules/core/test-res/edu/kit/iti/algover/smttrans".replace('/', File.separatorChar);
    private static final String config = "integerconfig.xml";
    private static final String mconfig = "IntegerModelConfig.xml";



    @Test
    public void loadExistingProject() throws Exception {
        ProjectManager pm = new ProjectManager(new File(dir), config);
        Project project = pm.getProject();

        PVCCollection allPVCs = project.getAllPVCs();

      
        for (PVC pvc : allPVCs.getContents()) {

            Proof proof = pm.getProofForPVC(pvc.getIdentifier());
            proof.setScriptText("z3;");
            proof.interpretScript();

            Assert.assertEquals(proof.getProofStatus(), ProofStatus.CLOSED);
            Assert.assertNull(proof.getFailException()); // ?

        }
        pm.saveProject();

    }


    private static String p1 = "negNumberModel/Post";
    private static String p2 = "numberModel/Post";
   // private static Map<String, Set<String>> modelDeclarations = new HashMap<>();
    private static Map<String, Set<String>> modelDefinitions = new HashMap<>();
    static {
     //   modelDeclarations.put(p1,
      //          new HashSet<String>(asList("~s2", ": SetInt", "~s1", ": SetInt", "setEmptyInt", ": SetInt")));
        modelDefinitions.put(p1, new HashSet<String>(asList("Def: ~i = 1",
                "Def: ~j = -1", "Def: ~k = 0")));

       // modelDeclarations.put(p2,
        //        new HashSet<String>(asList("~s2", ": SetInt", "~s1", ": SetInt", "setEmptyInt", ": SetInt")));
        modelDefinitions.put(p2, new HashSet<String>(asList("Def: ~k = 4","Def: ~j = 1","Def: ~i = 3")));

    }

    @Test
    public void modelTest() throws Exception {
        ProjectManager pm = new ProjectManager(new File(dir), mconfig);
        Project project = pm.getProject();

        PVCCollection allPVCs = project.getAllPVCs();

        for (PVC pvc : allPVCs.getContents()) {
            Proof proof = pm.getProofForPVC(pvc.getIdentifier());
            proof.setScriptText("z3;");
            try {

                proof.interpretScript();
            } catch (ScriptCommandNotApplicableException e) {
                Model m = Z3Rule.getModel();
              //  Assert.assertTrue(m.getDeclarations().isEmpty());
              //  Assert.assertTrue(m.getDeclarations().containsAll(modelDefinitions.get(pvc.getIdentifier())));
                
                Assert.assertNotEquals(proof.getProofStatus(), ProofStatus.CLOSED);

            }

        }
        pm.saveProject();

    }


}
