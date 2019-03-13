/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover;

import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.project.XMLProjectManager;
import org.junit.Ignore;
import org.junit.Test;

import java.io.File;

public class IntegrationTest {


    //Test that sumandmax is loadable and provable using z3
    @Ignore
    @Test
    public void testSumAndMax() throws Exception {
        String dirStr = "modules/core/test-res/edu/kit/iti/algover/examples".
                replace('/', File.separatorChar);
        // System.out.println(dir);
        File dir = new File(dirStr);

        //config file
        String config = "config.xml";

        //project manager should load project -> this parses all DafnyFiles, creates the PVCs, and empty proofWithTwoSubstitutionsAndSkips objects
        ProjectManager pm = new XMLProjectManager(dir, config);
        //get all proofs
        pm.getPVCByNameMap().forEach((s, pvc) -> System.out.println("pvc.getName() = " + pvc.getIdentifier()));
        //apply Z3 on all PVCs and build proofs+script
        pm.getAllProofs().forEach((s, proof) -> {
            proof.setScriptTextAndInterpret("fake");
        });

    }

    @Ignore
    @Test
    public void testSimple() throws Exception {
        String dir = "modules/core/test-res/edu/kit/iti/algover/script".
                replace('/', File.separatorChar);
        System.out.println(dir);
        //config file
        String config = "config.xml";

        //project manager should load project -> this parses all DafnyFiles, creates the PVCs, and empty proofWithTwoSubstitutionsAndSkips objects
        ProjectManager pm = new XMLProjectManager(new File(dir), config);
        //get all proofs
        pm.getPVCByNameMap().forEach((s, pvc) -> System.out.println("pvc.getName() = " + pvc.getIdentifier()));
        //apply Z3 on all PVCs and build proofs+script
        pm.getAllProofs().forEach((s, proof) -> proof.setScriptTextAndInterpret("fake"));
    }
}
