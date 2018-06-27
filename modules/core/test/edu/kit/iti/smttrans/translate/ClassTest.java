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

public class ClassTest {


    private static final String dir = "modules/core/test-res/edu/kit/iti/algover/smttrans".replace('/',
            File.separatorChar);
    
    private static final String oconfig = "classconfig.xml";
    
    //TODO fails but is correct 
    @Test
    public void closedProofsTest() throws Exception {
    ProjectManager pm = new ProjectManager(new File(dir), oconfig);
    Project project = pm.getProject();
   
    PVCCollection allPVCs = project.getAllPVCs();
   
    // TODO project.getPVCByName(name)
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
