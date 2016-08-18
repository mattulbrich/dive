package edu.kit.iti.algover.project;

import edu.kit.iti.algover.settings.ProjectSettings;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import java.io.File;
import java.util.LinkedList;
import java.util.List;

import static org.junit.Assert.assertEquals;


/**
 * Created by sarah on 8/18/16.
 * */

public class ProjectTest {
    Project p = null;

    String testDir = "modules/core/test-res/edu/kit/iti/algover/project";

    @Before
    public void prepare(){

        final File f1 = new File(testDir);

        ProjectBuilder pb = new ProjectBuilder();

        Project p = null;

        try {
            p = pb.buildProject(f1);
        } catch (Exception e) {
            e.printStackTrace();
        }
        this.p = p;

    }
    @Test
    public void testProjectImports(){

        List<File> dafnyFiles = p.getDafnyFiles();
        List<File> filesToTest = new LinkedList<>();
        filesToTest.add(new File(testDir+File.separator+"test.dfy"));
        filesToTest.add(new File(testDir+File.separator+"test2.dfy"));
        assertEquals(dafnyFiles, filesToTest);
    }

    @Test
    public void testLibImports(){
        List<File> dafnyFiles = p.getLibraries();
        List<File> filesToTest = new LinkedList<>();
        filesToTest.add(new File(testDir+File.separator+"test3.dfy"));
        assertEquals(dafnyFiles, filesToTest);
    }

    @Test
    public void testSettings(){
        ProjectSettings testSettings = p.getSettings();
        String value = testSettings.getValue(ProjectSettings.DAFNY_TIMEOUT);
        assertEquals(Integer.parseInt(value), 24);
    }

    //TODO test that classes and functions are correctly extracted
}
