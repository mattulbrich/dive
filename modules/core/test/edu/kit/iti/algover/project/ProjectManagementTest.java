package edu.kit.iti.algover.project;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import java.io.File;

/**
 * Tests for the methods for ProjectManagement
 */
public class ProjectManagementTest {

    static final String testDir = ("modules/core/test-res/edu/kit/iti/algover/script").replace('/', File.separatorChar);
    static final File config = new File(testDir + File.separatorChar + "config2.xml");
    Project p = null;

    @Before
    public void prepare() throws Exception {

        final File f1 = new File(testDir);

        ProjectBuilder pb = new ProjectBuilder();
        pb.setDir(f1);
        pb.setConfigFilename("config2.xml");
        pb.parseProjectConfigurationFile();
        Project p = pb.build();
        this.p = p;

    }

    @Test
    public void loadExistingProject() {
        ProjectManagement pm = new ProjectManagement();
        pm.loadProject(config);
        // Project project = pm.getProject();

        // Assert.assertEquals("Number of DafnyFiles", p.getDafnyFiles().size(), project.getDafnyFiles().size());
        Assert.assertEquals("config2.xml", pm.getConfigFile().getName());
        //PVCGroup pvcs = pm.getAllPVCs();

        //PVCs gegenchecken
        //TODO PVCs erzeugen und dagegen pruefen
        //Proof proof = pm.getProof(pvcName);
        //Assert.assertEquals(Status.DIRTY, proof.getStatus());
        //pm.replayAllProofs();
        //for (Proof pr : pm.getAllProofs()) {
        //    AssertEquals(Status.NON_EXISTING, pr.getStatus());
        //}

    }

}
