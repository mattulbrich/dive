package edu.kit.iti.algover.smttrans.translate;

import java.io.File;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.junit.Assert;
import org.junit.Test;

import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.PVCCollection;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofStatus;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.script.exceptions.ScriptCommandNotApplicableException;

public class DafnyExampleTest {

    private static final String dir = "modules/core/test-res/edu/kit/iti/algover/smttrans/translate/examples"
            .replace('/', File.separatorChar);

    private static final List<String> config = Arrays.asList("BinarySearchConfig.xml", "TuringFactorialConfig.xml",
            "FibConfig.xml", "FindConfig.xml", "FindZeroConfig.xml", "MaxSegSumConfig.xml", "CubesConfig.xml",
            "BubbleSortConfig.xml", "InsertionSortConfig.xml", "SelectionSortConfig.xml", "Pow2Config.xml", "QuickSortConfig.xml");


    @Test
    public void closedProofsTest() throws Exception {

        for (String c : config) {

            ProjectManager pm = new ProjectManager(new File(dir), c);
            Project project = pm.getProject();

            PVCCollection allPVCs = project.getAllPVCs();

            for (PVC pvc : allPVCs.getContents()) {

                Proof proof = pm.getProofForPVC(pvc.getIdentifier());

                 try {

                proof.setScriptText("z3;");
                proof.interpretScript();
                 } catch (ScriptCommandNotApplicableException e) {
                 System.out.println(pvc.getIdentifier());
                 continue;
                 }
                 if (!proof.getProofStatus().equals(ProofStatus.CLOSED)) {
                 System.out.println(pvc.getIdentifier());
                 }



            }
            pm.saveProject();
        }
    }
}
