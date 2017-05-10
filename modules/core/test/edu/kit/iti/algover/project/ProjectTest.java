/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.project;

import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.settings.ProjectSettings;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import java.io.File;
import java.io.FileNotFoundException;
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
    public void prepare() throws Exception {

        final File f1 = new File(testDir);

        ProjectBuilder pb = new ProjectBuilder();

        Project p = null;

        p = pb.buildProject(f1);
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

    @Test
    public void testMethodExtraction(){
        assertEquals(p.getClasses().size(), 1);
        List<DafnyMethod> methods = p.getClasses().get(0).getMethods();

        List<String> methodNames = new LinkedList<>();
        List<String> methodsString = new LinkedList<>();
        methodsString.add("arrayUpdate");
        methodsString.add("foo");
        assertEquals(methods.size(), 2);
        for(DafnyMethod m: methods){
            methodNames.add(m.getName());
        }
        assertEquals(methodNames, methodsString);


    }
    //TODO test that classes and functions are correctly extracted
}
