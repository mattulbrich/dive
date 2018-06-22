package edu.kit.iti.smttrans.translate;

import java.io.File;

import org.junit.Assert;
import org.junit.Test;

import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.PVCCollection;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofStatus;

public class Arr1Test {
    private static final String testDir = "modules/core/test-res/edu/kit/iti/algover/smttrans".replace('/', File.separatorChar);
    private static final String config = "arr1config.xml";




    @Test
    public void loadExistingProject() throws Exception {
        ProjectManager pm = new ProjectManager(new File(testDir), config);
        Project project = pm.getProject();

        PVCCollection allPVCs = project.getAllPVCs();

      
        for (PVC pvc : allPVCs.getContents()) {

            Proof proof = pm.getProofForPVC(pvc.getIdentifier());
            proof.setScriptText("z3;");
            proof.interpretScript();

            Assert.assertEquals(proof.getProofStatus(), ProofStatus.CLOSED);
            Assert.assertNull(proof.getFailException());

        }
        pm.saveProject();

    }


}
