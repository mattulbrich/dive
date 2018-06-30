package edu.kit.iti.smttrans.translate;

import java.io.File;
import static java.util.Arrays.asList;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

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
import edu.kit.iti.algover.rules.impl.Z3Rule;
import edu.kit.iti.algover.script.exceptions.ScriptCommandNotApplicableException;
import edu.kit.iti.algover.smttrans.access.Model;
import edu.kit.iti.algover.term.Sequent;

public class SetTest {

    private static final String dir = "modules/core/test-res/edu/kit/iti/algover/smttrans".replace('/',
            File.separatorChar);
    // private static final String cconfig = "setsconfig.xml";

    // private static final String mDir =
    // "modules/core/test-res/edu/kit/iti/algover/smttrans".replace('/',
    // File.separatorChar);
    private static final String mconfig = "setModelConfig.xml";
    private static final String oconfig = "setsconfig.xml";
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

    private static String p1 = "setOP/Post";
    private static String p2 = "intersect/Post";
    private static Map<String, Set<String>> modelDeclarations = new HashMap<>();
    private static Map<String, Set<String>> modelDefinitions = new HashMap<>();
    static {
        modelDeclarations.put(p1,
                new HashSet<String>(asList("~s2", ": Set<Int>", "~s1", ": Set<Int>", "setEmpty<Int>", ": Set<Int>")));
        modelDefinitions.put(p1, new HashSet<String>(asList("setInsert<Int> ((x!0 Int) (x!1 Set<Int>)) Set<Int> ~s2",
                "setcard<Int>!3(setEmpty<Int>) = 0", "setcard<Int>!3(~s2) = 5", "setcard<Int>!4(default) = 1")));

        modelDeclarations.put(p2,
                new HashSet<String>(asList("~s2", ": Set<Int>", "~s1", ": Set<Int>", "setEmpty<Int>", ": Set<Int>")));
        modelDefinitions.put(p2, new HashSet<String>(asList("setcard<Int>!16(setEmpty<Int>) = 0",
                "setcard<Int>!16(Set<Int>!val!3) = 5", "setcard<Int>!16(default) = 6")));

    }
    
    
    private boolean checkContent(Collection<String> c1, Collection<String> c2) {
        
       return false; 
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
               // Assert.assertTrue(m.getDeclarations().containsAll(modelDeclarations.get(pvc.getIdentifier())));
               // Assert.assertTrue(m.getDefinitions().containsAll(modelDefinitions.get(pvc.getIdentifier())));
                
                
                Assert.assertNotEquals(proof.getProofStatus(), ProofStatus.CLOSED);

            }

        }
        pm.saveProject();

    }
}
