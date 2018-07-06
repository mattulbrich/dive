package edu.kit.iti.algover.smttrans.translate;

import java.io.File;
import java.util.Arrays;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;

import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.PVCCollection;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofStatus;
import edu.kit.iti.algover.rules.RuleException;

public class DafnyExampleTest {

    private static final String dir = "modules/core/test-res/edu/kit/iti/algover/smttrans/translate/examples".replace('/',
            File.separatorChar);

    private static final List<String> config = Arrays.asList("BinarySearchConfig.xml"); //,"FibConfig.xml",
           // "FindZeroConfig.xml", "MaxSegSumConfig.xml", "FindConfig.xml");

    @Test
    public void closedProofsTest() throws Exception {

        for (String c : config) {

            ProjectManager pm = new ProjectManager(new File(dir), c);
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
}
