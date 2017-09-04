package edu.kit.iti.algover;

import edu.kit.iti.algover.project.ProjectManager;
import org.junit.Ignore;
import org.junit.Test;

import java.io.File;

public class IntegrationTest {


    //Test that sumandmax is loadable and provable using z3
    @Ignore
    @Test
    public void testSumAndMax() throws Exception {
        String dir = "modules/core/test-res/edu/kit/iti/algover/examples".
                replace('/', File.separatorChar);
        System.out.println(dir);
        //config file
        File config = new File(dir + File.separatorChar + "config.xml");

        ProjectManager pm = new ProjectManager();

        //project manager should load project -> this parses all DafnyFiles, creates the PVCs, and empty proof objects
        pm.loadProject(config);
        //get all proofs
        pm.getAllStrippedPVCs().forEach((s, pvc) -> System.out.println("pvc.getName() = " + pvc.getName()));
        //apply Z3 on all PVCs and build proofs+script
        pm.getAllProofs().forEach((s, proof) -> proof.interpretASTNode("fake"));

    }

    @Ignore
    @Test
    public void testSimple() throws Exception {
        String dir = "modules/core/test-res/edu/kit/iti/algover/script".
                replace('/', File.separatorChar);
        System.out.println(dir);
        //config file
        File config = new File(dir + File.separatorChar + "config.xml");

        ProjectManager pm = new ProjectManager();

        //project manager should load project -> this parses all DafnyFiles, creates the PVCs, and empty proof objects
        pm.loadProject(config);
        //get all proofs
        pm.getAllStrippedPVCs().forEach((s, pvc) -> System.out.println("pvc.getName() = " + pvc.getName()));
        //apply Z3 on all PVCs and build proofs+script
        pm.getAllProofs().forEach((s, proof) -> proof.interpretASTNode("fake"));
    }
}
