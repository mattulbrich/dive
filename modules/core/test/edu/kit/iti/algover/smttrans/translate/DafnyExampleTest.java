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
            "BubbleSortConfig.xml", "InsertionSortConfig.xml", "SelectionSortConfig.xml","Pow2Config.xml");
    // ERRORS:,
    // ,"QuickSortConfig.xml",

    
    // known errors/timeouts
    private static final Set<String> excepted = new HashSet<>(Arrays.asList("FindZero/loop/Bounds",
            "FindZero/loop/else/EstPre[Lemma].3", "FindZero/loop/else/Dec", "FindZero/loop/else/Bounds",
            "FindZero/loop/then/Post.1", "Lemma/then/Dec[Lemma]", "MaxSegSum/InitInv", "MaxSegSum/loop/else/else/Dec",
            "MaxSegSum/loop/else/then/Dec", "MaxSegSum/loop/then/Dec", "Cubes/loop/Dec", "BubbleSort/InitInv.2",
            "BubbleSort/loop/loop/then/Dec", "BubbleSort/loop/loop/then/Modifies",
            "BubbleSort/loop/loop/then/Modifies.1", "BubbleSort/loop/loop_exit/Dec", "InsertionSort/InitInv.1",
            "InsertionSort/loop/Modifies", "InsertionSort/loop/InitInv", "InsertionSort/loop/loop/Modifies",
            "InsertionSort/loop/loop_exit/Dec", "InsertionSort/loop/loop_exit/Modifies", "SelectionSort/InitInv.1",
            "SelectionSort/loop/loop/then/Dec", "SelectionSort/loop/loop_exit/Dec",
            "SelectionSort/loop/loop_exit/Modifies", "SelectionSort/loop/loop_exit/Modifies.1","Theorem/else/else/Dec[Theorem]","Theorem/else/then/Dec[Theorem]"));


    @Test
    public void closedProofsTest() throws Exception {

        for (String c : config) {

            ProjectManager pm = new ProjectManager(new File(dir), c);
            Project project = pm.getProject();

            PVCCollection allPVCs = project.getAllPVCs();

            for (PVC pvc : allPVCs.getContents()) {

                Proof proof = pm.getProofForPVC(pvc.getIdentifier());
                if (excepted.contains(pvc.getIdentifier()))
                    continue;
//               try {

                    proof.setScriptText("z3;");
                    proof.interpretScript();
//                } catch (ScriptCommandNotApplicableException e) {
//                    System.out.println(pvc.getIdentifier());
//                    continue;
//                }
//                if (!proof.getProofStatus().equals(ProofStatus.CLOSED)) {
//                    System.out.println(pvc.getIdentifier());
//                }
                 if (!excepted.contains(pvc.getIdentifier())) {
                
                 Assert.assertEquals(proof.getProofStatus(), ProofStatus.CLOSED);
                 Assert.assertNull(proof.getFailException());
                 }

            }
            pm.saveProject();
        }
    }
}
